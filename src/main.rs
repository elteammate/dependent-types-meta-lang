use std::collections::{HashMap, VecDeque};
use std::fmt::{Display, Formatter};
use std::rc::Rc;
use smol_str::SmolStr;

/// A name in the lambda calculus.
/// Either a bound variable defined by its de Bruijn index,
/// or a free variable defined by its name.
#[derive(PartialEq, Debug, Clone)]
enum Name {
    Bound(usize),
    Free(SmolStr),
}

/// An externally defined value
#[derive(PartialEq, Clone)]
enum EValue {
    Int(i64),
    IntTy,
}

type Type = Rc<Term>;

#[derive(PartialEq)]
enum Term {
    Var { name: Name },
    Value { value: EValue },
    App { head: Rc<Term>, app: Rc<Term> },
    Lam { body: Rc<Term>, ty: Type },
    Pi { body: Rc<Term>, ty: Type },
    Star(usize),
}

impl EValue {
    fn ty(&self) -> Rc<Term> {
        let int = Rc::new(Term::Value { value: EValue::IntTy });
        match self {
            EValue::Int(_) => Rc::new(Term::Value { value: EValue::IntTy }),
            EValue::IntTy => Rc::new(Term::Star(0)),
        }
    }
}

fn substitute_top(term: Rc<Term>, sub: Rc<Term>) -> Rc<Term> {
    fn substitute(term: Rc<Term>, sub: Rc<Term>, i: usize) -> Rc<Term> {
        match &*term {
            Term::Var { name } => {
                match name {
                    Name::Bound(j) if *j > i => Rc::new(Term::Var { name: Name::Bound(j - 1) }),
                    Name::Bound(j) if *j == i => sub,
                    Name::Bound(_) => term,
                    Name::Free(_) => term,
                }
            }
            Term::Value { .. } => term,
            Term::App { head, app } => {
                let head = substitute(head.clone(), sub.clone(), i);
                let app = substitute(app.clone(), sub.clone(), i);
                Rc::new(Term::App { head, app })
            }
            Term::Lam { body, ty } => {
                let ty = substitute(ty.clone(), sub.clone(), i);
                let body = substitute(body.clone(), sub.clone(), i + 1);
                Rc::new(Term::Lam { body, ty })
            }
            Term::Pi { body, ty } => {
                let ty = substitute(ty.clone(), sub.clone(), i);
                let body = substitute(body.clone(), sub.clone(), i + 1);
                Rc::new(Term::Pi { body, ty })
            }
            Term::Star(_) => term,
        }
    }

    substitute(term, sub, 0)
}

fn shift_indices(term: Rc<Term>, d: isize) -> Rc<Term> {
    fn shift(term: Rc<Term>, d: isize, c: usize) -> Rc<Term> {
        match &*term {
            Term::Var { name } => {
                match name {
                    Name::Bound(i) if *i >= c =>
                        Rc::new(Term::Var { name: Name::Bound(((*i as isize) + d) as usize) }),
                    Name::Bound(_) => term,
                    Name::Free(_) => term,
                }
            }
            Term::Value { .. } => term,
            Term::App { head, app } => {
                let head = shift(head.clone(), d, c);
                let app = shift(app.clone(), d, c);
                Rc::new(Term::App { head, app })
            }
            Term::Lam { body, ty } => {
                let ty = shift(ty.clone(), d, c);
                let body = shift(body.clone(), d, c + 1);
                Rc::new(Term::Lam { body, ty })
            }
            Term::Pi { body, ty } => {
                let ty = shift(ty.clone(), d, c);
                let body = shift(body.clone(), d, c + 1);
                Rc::new(Term::Pi { body, ty })
            }
            Term::Star(_) => term,
        }
    }

    shift(term, d, 0)
}

fn replace_with_index(term: Rc<Term>, name: SmolStr, level: usize) -> Rc<Term> {
    match &*term {
        Term::Var { name: Name::Free(n) } if *n == name => {
            Rc::new(Term::Var { name: Name::Bound(level) })
        }
        Term::Value { .. } => term,
        Term::Var { .. } => term,
        Term::App { app, head } => {
            let app = replace_with_index(app.clone(), name.clone(), level);
            let head = replace_with_index(head.clone(), name.clone(), level);
            Rc::new(Term::App { app, head })
        }
        Term::Lam { ty, body } => {
            let ty = replace_with_index(ty.clone(), name.clone(), level);
            let body = replace_with_index(body.clone(), name.clone(), level + 1);
            Rc::new(Term::Lam { ty, body })
        }
        Term::Pi { ty, body } => {
            let ty = replace_with_index(ty.clone(), name.clone(), level);
            let body = replace_with_index(body.clone(), name.clone(), level + 1);
            Rc::new(Term::Pi { ty, body })
        }
        Term::Star(_) => term,
    }
}

fn lambda_abstract(term: Rc<Term>, name: SmolStr, ty: Type) -> Rc<Term> {
    let term = replace_with_index(term, name, 0);
    Rc::new(Term::Lam { ty, body: term })
}

fn pi_abstract(term: Rc<Term>, name: SmolStr, ty: Type) -> Rc<Term> {
    let term = replace_with_index(term, name, 0);
    Rc::new(Term::Pi { ty, body: term })
}

fn nf(term: Rc<Term>) -> Rc<Term> {
    match &*term {
        Term::Var { name: _ } => term,
        Term::Value { value: _ } => term,
        Term::Lam { body, ty } => {
            let body = nf(body.clone());
            let ty = nf(ty.clone());
            Rc::new(Term::Lam { body, ty })
        }
        Term::Pi { body, ty } => {
            let body = nf(body.clone());
            let ty = nf(ty.clone());
            Rc::new(Term::Pi { body, ty })
        }
        Term::App { head, app } => {
            let head = nf(head.clone());
            let app = nf(app.clone());
            match &*head {
                Term::Lam { body, ty: _ } => {
                    let body = nf(body.clone());
                    nf(substitute_top(body, app))
                }
                _ => term
            }
        }
        Term::Star(_) => term,
    }
}

struct Env {
    ext: HashMap<SmolStr, Type>,
    int: VecDeque<Type>,
}

impl Env {
    fn new() -> Self {
        Self {
            ext: HashMap::new(),
            int: VecDeque::new(),
        }
    }

    fn push(&mut self, ty: Type) {
        self.int.push_front(ty);
        // println!("Env state:");
        // for i in 0..self.int.len() {
        //     println!("@{}: {}", i, self.get(&Name::Bound(i)).unwrap());
        // }
    }

    fn pop(&mut self) {
        self.int.pop_front();
        // println!("Env state:");
        // for i in 0..self.int.len() {
        //     println!("@{}: {}", i, self.get(&Name::Bound(i)).unwrap());
        // }
    }

    fn get(&self, name: &Name) -> Option<Type> {
        match name {
            Name::Bound(i) => {
                let shift = *i as isize + 1;
                self.int.get(*i).map(|ty| shift_indices(ty.clone(), shift))
            }
            Name::Free(s) => self.ext.get(s).cloned(),
        }
    }
}

fn type_check(env: &mut Env, term: Rc<Term>) -> Result<Type, String> {
    match &*term {
        Term::Var { name } => {
            match env.get(name) {
                Some(ty) => Ok(ty.clone()),
                None => Err(format!("Unbound variable: {}", name)),
            }
        }
        Term::Value { value } => {
            Ok(value.ty())
        }
        Term::App { head, app } => {
            let head_ty = type_check(env, head.clone())?;
            let app_ty = type_check(env, app.clone())?;
            // (head:head_ty) (app:app_ty)
            match &*head_ty {
                Term::Pi { ty, body: result_ty } => {
                    // (head:(pi ty. result_ty)) (app:app_ty)
                    // TODO: is this nf necessary?
                    if nf(ty.clone()) == app_ty {
                        Ok(substitute_top(result_ty.clone(), app.clone()))
                    } else {
                        Err(format!("Type mismatch: head had type {}, but applied value had type {}", head_ty, app_ty))
                    }
                }
                _ => Err("Non-function application".to_string()),
            }
        }
        Term::Lam { ty, body } => {
            let _ = type_check(env, ty.clone())?;
            env.push(ty.clone());
            let body_ty = type_check(env, body.clone())?;
            env.pop();
            // println!("Lam: {} {}", ty, body_ty);
            let ty = Rc::new(Term::Pi { body: body_ty, ty: ty.clone() });
            let _ = type_check(env, ty.clone())?;
            Ok(ty)
        }
        Term::Pi { ty, body } => {
            // println!("Pi: {} {}", ty, body);
            let ty_ty = type_check(env, ty.clone())?;
            env.push(ty.clone());
            let body_ty = shift_indices(type_check(env, body.clone())?, -1);
            env.pop();
            let Term::Star(_) = &*ty_ty else {
                return Err(format!("Pi bound type must be a universal type, but is {}", ty_ty));
            };
            let Term::Star(_) = &*body_ty else {
                return Err(format!("Pi body type must be a universal type, but is {}", body_ty));
            };
            Ok(body_ty)
        }
        Term::Star(level) => {
            Ok(Rc::new(Term::Star(level + 1)))
        }
    }
}

impl Display for Name {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Name::Bound(i) => write!(f, "@{}", i),
            Name::Free(s) => write!(f, "{}", s),
        }
    }
}

impl Display for EValue {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            EValue::Int(i) => write!(f, "{}", i),
            EValue::IntTy => write!(f, "Int"),
        }
    }
}

impl Display for Term {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Term::Var { name } => write!(f, "{}", name),
            Term::Value { value } => write!(f, "{}", value),
            Term::App { head, app } => write!(f, "({} {})", head, app),
            Term::Lam { body, ty } => write!(f, "(λ:{}. {})", ty, body),
            Term::Pi { body, ty } => write!(f, "(Π:{}. {})", ty, body),
            Term::Star(level) => write!(f, "Type({})", level),
        }
    }
}

macro_rules! t {
    (/ $var:ident: $ty:expr, $body:expr) => {
        lambda_abstract($body, SmolStr::new(stringify!($var)), $ty)
    };
    (# $var:ident: $ty:expr, $body:expr) => {
        pi_abstract($body, SmolStr::new(stringify!($var)), $ty)
    };
    (Type) => {
        Rc::new(Term::Star(0))
    };
    (Int) => {
        Rc::new(Term::Value { value: EValue::IntTy })
    };
    ($var:ident) => {
        Rc::new(Term::Var { name: Name::Free(SmolStr::new(stringify!($var))) })
    };
    ($value:literal) => {
        Rc::new(Term::Value { value: EValue::Int($value) })
    };
    ($head:expr; $app:expr) => {
        Rc::new(Term::App { head: $head, app: $app })
    };
}

enum UTerm {
    Var { name: Name },
    Value { value: EValue },
    App { head: Rc<Term>, app: Rc<Term> },
    ULam { body: Rc<Term> },
    UPi { body: Rc<Term> },
    Lam { body: Rc<Term>, ty: Type },
    Pi { body: Rc<Term>, ty: Type },
    Ann { term: Rc<Term>, ty: Type },
    Hole,
    Star(usize),
}

enum AUTerm {
    TVar { id: usize },
    Var { name: Name },
    Value { value: EValue },
    App { head: Rc<AUTerm>, app: Rc<AUTerm> },
    Lam { body: Rc<AUTerm>, ty: Rc<AUTerm> },
    Pi { body: Rc<AUTerm>, ty: Rc<AUTerm> },
    Star(usize),
}

impl Display for AUTerm {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            AUTerm::TVar { id } => write!(f, "'{}", id),
            AUTerm::Var { name } => write!(f, "{}", name),
            AUTerm::Value { value } => write!(f, "{}", value),
            AUTerm::App { head, app } => write!(f, "({} {})", head, app),
            AUTerm::Lam { body, ty } => write!(f, "(λ:{}. {})", ty, body),
            AUTerm::Pi { body, ty } => write!(f, "(Π:{}. {})", ty, body),
            AUTerm::Star(level) => write!(f, "Type({})", level),
        }
    }
}

fn to_au(term: Rc<Term>) -> Rc<AUTerm> {
    match &*term {
        Term::Var { name } => {
            Rc::new(AUTerm::Var { name: name.clone() })
        }
        Term::Value { value } => {
            Rc::new(AUTerm::Value { value: value.clone() })
        }
        Term::App { head, app } => {
            let head = to_au(head.clone());
            let app = to_au(app.clone());
            Rc::new(AUTerm::App { head, app })
        }
        Term::Lam { body, ty } => {
            let body = to_au(body.clone());
            let ty = to_au(ty.clone());
            Rc::new(AUTerm::Lam { body, ty })
        }
        Term::Pi { body, ty } => {
            let body = to_au(body.clone());
            let ty = to_au(ty.clone());
            Rc::new(AUTerm::Pi { body, ty })
        }
        Term::Star(level) => Rc::new(AUTerm::Star(*level)),
    }
}

fn maybe_reduce(term: Rc<AUTerm>) -> Option<Rc<AUTerm>> {
    match &*term {
        AUTerm::TVar { .. } => None,
        AUTerm::Var { .. } => None,
        AUTerm::Value { .. } => None,
        AUTerm::App { .. } => {}
        AUTerm::Lam { .. } => {}
        AUTerm::Pi { .. } => {}
        AUTerm::Star(_) => None,
    }
}

struct Solver<'a> {
    env: &'a Env,
    assignment: Vec<Option<Rc<AUTerm>>>,
}

impl<'a> Solver<'a> {
    fn new(env: &'a Env) -> Self {
        Self {
            env,
            assignment: Vec::new(),
        }
    }

    fn fresh(&mut self) -> Rc<AUTerm> {
        let id = self.assignment.len();
        self.assignment.push(None);
        Rc::new(AUTerm::TVar { id })
    }

    fn repr(&mut self, ty: Rc<AUTerm>) -> Rc<AUTerm> {
        let id = match &*ty {
            AUTerm::TVar { id } => *id,
            _ => return ty,
        };
        match &self.assignment[id] {
            Some(term) => {
                match &**term {
                    AUTerm::TVar { id: _ } => self.repr(term.clone()),
                    _ => term.clone(),
                }
            }
            None => Rc::new(AUTerm::TVar { id }),
        }
    }

    fn occurs_in(&mut self, id: usize, term: Rc<AUTerm>) -> bool {
        let term = self.repr(term);
        match &*term {
            AUTerm::TVar { id: id2 } => id == *id2,
            AUTerm::Var { name: _ } => false,
            AUTerm::Value { value: _ } => false,
            AUTerm::App { head, app } => {
                self.occurs_in(id, head.clone()) || self.occurs_in(id, app.clone())
            }
            AUTerm::Lam { body, ty } => {
                self.occurs_in(id, body.clone()) || self.occurs_in(id, ty.clone())
            }
            AUTerm::Pi { body, ty } => {
                self.occurs_in(id, body.clone()) || self.occurs_in(id, ty.clone())
            }
            AUTerm::Star(_) => false,
        }
    }

    fn unify(&mut self, t1: Rc<AUTerm>, t2: Rc<AUTerm>) -> Result<(), String> {
        let t1 = self.repr(t1);
        let t2 = self.repr(t2);
        match (&*t1, &*t2) {
            (AUTerm::TVar { id: id1 }, AUTerm::TVar { id: id2 })
            if id1 == id2 =>
                Ok(()),

            (AUTerm::TVar { id: id1 }, _) => {
                if self.occurs_in(*id1, t2.clone()) {
                    return Err(format!("Occurs check failed: {} occurs in {}", t1, t2));
                }
                self.assignment[*id1] = Some(t2.clone());
                Ok(())
            }
            (_, AUTerm::TVar { id: id2 }) => {
                if self.occurs_in(*id2, t1.clone()) {
                    return Err(format!("Occurs check failed: {} occurs in {}", t2, t1));
                }
                self.assignment[*id2] = Some(t1.clone());
                Ok(())
            }
            (AUTerm::App { head: head1, app: app1 }, AUTerm::App { head: head2, app: app2 }) => {
                self.unify(head1.clone(), head2.clone())?;
                self.unify(app1.clone(), app2.clone())
            }
            (AUTerm::Lam { body: body1, ty: ty1 }, AUTerm::Lam { body: body2, ty: ty2 }) => {
                self.unify(body1.clone(), body2.clone())?;
                self.unify(ty1.clone(), ty2.clone())
            }
            (AUTerm::Pi { body: body1, ty: ty1 }, AUTerm::Pi { body: body2, ty: ty2 }) => {
                self.unify(body1.clone(), body2.clone())?;
                self.unify(ty1.clone(), ty2.clone())
            }
            (AUTerm::Star(level1), AUTerm::Star(level2)) if level1 == level2 => Ok(()),
            (AUTerm::Var { name: name1 }, AUTerm::Var { name: name2 }) if name1 == name2 => Ok(()),
            (AUTerm::Value { value: value1 }, AUTerm::Value { value: value2 }) if value1 == value2 => Ok(()),
            _ => Err(format!("Unification failed: {} != {}", t1, t2)),
        }
    }
}

fn main() {
    let mut env = Env::new();
    let id = t!(/a: t!(Type), t!(/x: t!(a), t!(x)));
    // let id = t!(/x: t!(Int), t!(x));
    println!("{}", id);
    let ty = type_check(&mut env, id.clone()).unwrap();
    println!("{}", ty);
    let ty_ty = type_check(&mut env, ty.clone()).unwrap();
    println!("{}", ty_ty);

    let const_ = t!(/a: t!(Type), t!(/b: t!(Type), t!(/x: t!(a), t!(/y: t!(b), t!(x)))));
    println!("{}", const_);
    let ty = type_check(&mut env, const_.clone()).unwrap();
    println!("{}", ty);
    let ty_ty = type_check(&mut env, ty.clone()).unwrap();
    println!("{}", ty_ty);

    let const_app = t!(t!(const_; t!(Int)); t!(Int));
    println!("{}", const_app);
    println!("{}", nf(const_app.clone()));
    println!("{}", nf(t!(t!(const_app; t!(1)); t!(5))));
}
