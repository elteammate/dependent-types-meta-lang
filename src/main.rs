use std::rc::Rc;
use std::collections::HashMap;
use smol_str::SmolStr;

#[derive(Clone, PartialEq)]
enum Name {
    Free(SmolStr),
    Bound(usize),
}

#[derive(Clone, PartialEq)]
enum TermI {
    Star,
    Var { name: Name },
    Pi { abs: Rc<TermC>, term: Rc<TermC> },
    Ann { term: Rc<TermC>, ty: Rc<TermC> },
    App { head: Rc<TermI>, app: Rc<TermC> },
}

#[derive(Clone, PartialEq)]
enum TermC {
    I(Rc<TermI>),
    Lam { body: Rc<TermI> },
}

struct Env<'a> {
    ext: &'a HashMap<SmolStr, Rc<TermI>>,
    int: &'a mut Vec<Rc<TermI>>,
}

impl<'a> Env<'a> {
    fn get(&self, name: &Name) -> Option<Rc<TermI>> {
        match name {
            Name::Free(name) => self.ext.get(name).cloned(),
            Name::Bound(index) => self.int.get(self.int.len() - index - 1).cloned(),
        }
    }
}

fn substitute_top(term: Rc<TermI>, sub: Rc<TermI>) -> Rc<TermI> {
    fn substitute_c(i: usize, term: Rc<TermC>, sub: Rc<TermI>) -> Rc<TermC> {
        match &*term {
            TermC::I(term) => Rc::new(TermC::I(substitute_i(i, term.clone(), sub.clone()))),
            TermC::Lam { body } => {
                let body = substitute_i(i + 1, body.clone(), sub.clone());
                Rc::new(TermC::Lam { body })
            }
        }
    }
    
    fn substitute_i(i: usize, term: Rc<TermI>, sub: Rc<TermI>) -> Rc<TermI> {
        match &*term {
            TermI::Star => term,
            TermI::Var { name } => {
                match name {
                    Name::Free(_) => term,
                    Name::Bound(j) => {
                        if i == *j {
                            sub
                        } else if i < *j {
                            term
                        } else {
                            Rc::new(TermI::Var { name: Name::Bound(j - 1) })
                        }
                    }
                }
            }
            TermI::Pi { abs, term } => {
                let abs = substitute_c(i, abs.clone(), sub.clone());
                let term = substitute_c(i + 1, term.clone(), sub.clone());
                Rc::new(TermI::Pi { abs, term })
            }
            TermI::Ann { term, ty } => {
                let term = substitute_c(i, term.clone(), sub.clone());
                let ty = substitute_c(i, ty.clone(), sub.clone());
                Rc::new(TermI::Ann { term, ty })
            }
            TermI::App { head, app } => {
                let head = substitute_i(i, head.clone(), sub.clone());
                let app = substitute_c(i, app.clone(), sub.clone());
                Rc::new(TermI::App { head, app })
            }
        }
    }
    
    substitute_i(0, term, sub)
}

fn eval_i(env: &mut Env, term: Rc<TermI>) -> Rc<TermI> {
    match &*term {
        TermI::Star => term,
        TermI::Var { name } => {
            env.get(name).expect("Unbound Variable")
        }
        TermI::Pi { abs, term } => {
            let abs = eval_c(env, abs.clone());
            let term = eval_c(env, term.clone());
            Rc::new(TermI::Pi { abs, term })
        }
        TermI::Ann { term, ty } => {
            if let TermC::I(inferable) = &**term {
                eval_i(env, inferable.clone())
            } else {
                let term = eval_c(env, term.clone());
                let ty = eval_c(env, ty.clone());
                Rc::new(TermI::Ann { term, ty })
            }
        }
        TermI::App { app, head } => {
            let head = eval_i(env, head.clone());
            let app = eval_c(env, app.clone());
            if let TermI::Ann { term, ty } = &*head {
                match &**term {
                    TermC::I(inferable) => {
                        eval_i(env, Rc::new(TermI::App { head: inferable.clone(), app }))
                    }
                    TermC::Lam { body } => {
                        let ty = eval_c(env, ty.clone());
                        let TermC::I(ty) = (*ty).clone() else {
                            panic!("Type Annotation is not a closed term");
                        };
                        let TermI::Pi { term: result_ty, .. } = &*ty else {
                            panic!("Type Annotation is not a function type");
                        };
                        let app = Rc::new(TermI::Ann {
                            term: app,
                            ty: result_ty.clone(),
                        });
                        substitute_top(body.clone(), app)
                    }
                }
            } else {
                return Rc::new(TermI::App { app, head });
            }
        }
    }
}

fn eval_c(env: &mut Env, term: Rc<TermC>) -> Rc<TermC> {
    match &*term {
        TermC::I(term) => Rc::new(TermC::I(eval_i(env, term.clone()))),
        TermC::Lam { body } => {
            let body = eval_i(env, body.clone());
            Rc::new(TermC::Lam { body })
        }
    }
}

fn main() {
    println!("Hello, world!");
}
