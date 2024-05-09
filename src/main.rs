use std::rc::Rc;
use std::collections::HashMap;
use smol_str::SmolStr;

#[derive(Clone, PartialEq)]
enum Name {
    Free(SmolStr),
    Bound(usize),
}

#[derive(Clone, PartialEq)]
enum Term {
    Star,
    Var { name: Name, ty: Rc<Term> },
    Pi { abs: Rc<Term>, term: Rc<Term> },
    Lam { body: Rc<Term>, ty: Rc<Term> },
    App { head: Rc<Term>, app: Rc<Term> },
}

fn eval(env_ext: &HashMap<SmolStr, Rc<Term>>, env_int: &mut Vec<Option<Rc<Term>>>, term: Rc<Term>) -> Rc<Term> {
    match (*term).clone() {
        Term::Star => term,
        Term::Var { name: Name::Free(name), .. } =>
            env_ext.get(&name).expect("Undefined variable").clone(),
        Term::Var { name: Name::Bound(index), .. } =>
            if let Some(e) = env_int[env_int.len() - index - 1].clone() {
                e
            } else {
                term
            },
        Term::Pi { abs, term } => {
            let abs = eval(env_ext, env_int, abs);
            let term = eval(env_ext, env_int, term);
            Rc::new(Term::Pi { abs, term })
        }
        Term::Lam { body, ty } => {
            let body = eval(env_ext, env_int, body);
            env_int.push(None);
            let res = Rc::new(Term::Lam { body, ty });
            env_int.pop();
            res
        }
        Term::App { head, app } => {
            let app = eval(env_ext, env_int, app);
            let head = eval(env_ext, env_int, head);
            match &*head {
                Term::Lam { body, .. } => {
                    env_int.push(Some(app));
                    let res = eval(env_ext, env_int, body.clone());
                    env_int.pop();
                    res
                }
                _ => Rc::new(Term::App { head, app }),
            }
        }
    }
}

fn check_types(ctx_ext: &HashMap<SmolStr, Rc<Term>>, ctx_int: &mut Vec<Rc<Term>>, term: Rc<Term>) -> Result<Rc<Term>, SmolStr> {
    match (*term).clone() {
        Term::Star => Ok(term),
        Term::Var { name: Name::Free(name), ty } => {
            let ty_ty = check_types(ctx_ext, ctx_int, ty)?;
            if ty_ty != Rc::new(Term::Star) {
                return Err("Type mismatch: type of type should be star".into());
            }
            if let Some(expected) = ctx_ext.get(&name) {
                if expected == &ty {
                    Ok(term)
                } else {
                    Err("Type mismatch".into())
                }
            } else {
                Err("Undefined variable".into())
            }
        },
        Term::Var { name: Name::Bound(index), ty } => {
            if let Some(ty) = ctx_int.get(ctx_int.len() - index - 1) {
                Ok(ty.clone())
            } else {
                Err("Undefined variable".into())
            }
        }
            
        Term::Pi { abs, term } => {
            check_types(ctx_ext, ctx_int, abs)?;
            check_types(ctx_ext, ctx_int, term)
        }
        Term::Lam { body, ty } => {
            check_types(ctx_ext, ctx_int, ty)?;
            ctx_int.push(Some(ty));
            check_types(ctx_ext, ctx_int, body)?;
            ctx_int.pop();
            Ok(())
        }
        Term::App { head, app } => {
            check_types(ctx_ext, ctx_int, head)?;
            check_types(ctx_ext, ctx_int, app)
        }
    }
}

fn main() {
    println!("Hello, world!");
}
