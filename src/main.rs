/*
 * TODO: Remove this!!
 */
#![allow(warnings)]

use std::collections::VecDeque;

const LOGO: &str = r"                          _
                         | |
 ___  ___ ___  _ __ _ __ | |__   ___  __ _ _ __
/ __|/ __/ _ \| '__| '_ \| '_ \ / _ \/ _` | '__|
\__ \ (_| (_) | |  | | | | |_) |  __/ (_| | |
|___/\___\___/|_|  |_| |_|_.__/ \___|\__,_|_|

                                                ";
const expr1: &str = "(+ 3 4)";
const expr2: &str = "(* 2 (+ 3 4))";
const add_zero: &str = "(+ x 0)";
const zero_add: &str = "(+ 0 x)";
const program: &str = "(begin (define r 10) (* pi (* r r)))";

const neg1: Expr = Expr::IntLit(-1);

#[derive(Debug)]
enum Expr {
    IntLit(i32),
    FltLit(f32),
    Symbol(String),
    List(Box<[Expr]>), /* TODO: This would more elegantly (but inefficiently)
                        *       expressed as a Linked List.
                        */
}

/*
 * TODO: Perhaps write a functional version of this?
 */
fn concat(s: &mut String, t: &str) {
    /*
     * TODO: This function requires preconditions.
     */

    let bs = t.as_bytes();
    let n = bs.len();

    let mut i = 0;
    /*
     * Inv: TODO
     */
    while i < n {
        /*
         * TODO: What's the overheading of converting u8 to char?
         */
        s.push(bs[i] as char);
        i += 1;
    }

    /*
     * TODO: This function requires postconditions.
     */
}

#[inline(always)]
/*
 * TODO: Extend this to replacing arbitrary strings.
 */
fn replace(s: &str, c: u8, t: &str) -> String {
    /*
     * TODO: This function requires preconditions.
     */

    let bs = s.as_bytes();
    let n = bs.len();

    let mut i = 0;
    let mut acc = String::new();

    /*
     * Inv: acc is bs[0], ..., bs[i - 1] but for all j st bs[j] == c,
     * acc has the string t inserted instead of c.
     */
    while i < n {
        if bs[i] == c {
            concat(&mut acc, t);
        } else {
            acc.push(bs[i] as char);
        }
        i += 1;
    }

    /*
     * TODO This function requires postconditions.
     */
    acc
}

/*
 * TODO: Extend this to splitting on arbitrary strings.
 */
fn split(s: &str, c: u8) -> Vec<String> {
    /*
     * TODO: This function requires preconditions.
     */

    let bs = s.as_bytes();
    let n = bs.len();

    let mut i = 0;
    let mut acc = vec![];

    /*
     * Inv: TODO
     */
    while i < n {
        if bs[i] == c {
            i += 1;
        } else {
            let mut j = i + 1;

            /*
             * Inv: TODO
             */
            while j < n && bs[j] != c {
                j += 1;
            }
            /*
             * TODO: This is unsafe, and super inefficient!
             */
            acc.push(String::from_utf8_lossy(&bs[i..j]).into_owned());
            i = j;
        }
    }

    /*
     * TODO: This function requires postconditions.
     */
    acc
}

fn lex(s: &str) -> Vec<String> {
    /*
     * TODO: This function requires more preconditions.
     */
    debug_assert!(s == s.trim());

    /*
     * TODO: Is there a simpler way to write this?
     */
    let ts = split(&replace(&replace(s, b'(', " ( "), b')', " ) "), b' ');

    /*
     * TODO: This function requires more postconditions.
     */
    ts
}

fn atom_read(s: &str) -> Result<Expr, &'static str> {
    /*
     * TODO: This function needs more preconditions.
     */
    debug_assert!(s == s.trim());

    /*
     * TODO: This is really ugly.
     */
    let expr = match s.parse::<i32>() {
        Ok(n) => Ok(Expr::IntLit(n)),
        Err(_) => match s.parse::<f32>() {
            Ok(x) => Ok(Expr::FltLit(x)),
            Err(_) => Ok(Expr::Symbol(s.to_string())),
        },
    };

    /*
     * TODO: This function needs more postconditions.
     */
    expr
}

/*
 * TODO: How the hell was this algorithm derived?
 * TODO: I need to transform this into an iterative procedure using a stack. I
 *       don't want mutable references.
 */
fn tokens_read(ts: &mut VecDeque<String>) -> Result<Expr, &'static str> {
    /*
     * TODO: This procedure is missing preconditions.
     */

    /*
     * TODO: What is as_str() doing?
     * TODO: This code is really ugly.
     */
    let expr = match ts.pop_front() {
        Some(t) => match t.as_str() {
            "(" => {
                /*
                 * TODO: Why is this block correct?
                 */

                let mut xs = vec![];
                /*
                 * Inv: TODO
                 */
                while ts[0].as_str() != ")" {
                    xs.push(tokens_read(ts)?);
                }
                ts.pop_front();
                Ok(Expr::List(xs.into()))
            }
            ")" => Err("tokens_read: unexpected )"),
            c => atom_read(c),
        },
        None => Err("tokens_read: tokens must be nonempty"),
    };

    /*
     * TODO: This procedure is missing postconditions.
     */

    expr
}

fn read(s: &str) -> Result<Expr, &'static str> {
    /*
     * TODO: This procedure is missing preconditions
     */

    let expr = tokens_read(&mut VecDeque::from(lex(s)));

    /*
     * TODO: This procedure is missing postconditions.
     */
    expr
}

fn add_zero_lint(x: Expr) -> Option<String> {
    /*
     * TODO: This procedure is missing preconditions.
     */
    match x {
        Expr::IntLit(_) => None,
        Expr::FltLit(_) => None,
        Expr::Symbol(_) => None,
        Expr::List(xs) => match *xs {
            [Expr::Symbol(ref op), Expr::Symbol(ref x), Expr::IntLit(0)] if op == "+" => {
                Some(String::from("add_zero"))
            }
            [Expr::Symbol(ref op), Expr::IntLit(0), Expr::Symbol(ref x)] if op == "+" => {
                Some(String::from("add_zero"))
            }
            _ => None,
        },
    }
    /*
     * TODO: This procedure is missing postconditions.
     */
}

fn lint(x: Expr) -> Vec<String> {
    /*
     * TODO: This procedure is missing preconditions.
     */
    match add_zero_lint(x) {
        None => vec![],
        Some(s) => vec![s]
    }
    /*
     * TODO: This procedure is missing postconditions.
     */
}

/* TODO */
fn raise(x: Expr) -> Expr {
    todo!()
}

fn main() {
    println!("{}", LOGO);
}

#[cfg(test)]
mod test {
    use super::*;
    use expect_test::{Expect, expect};
    use std::fmt::Debug;

    fn str_check<T: ToString>(actual: T, expect: Expect) {
        let actual = actual.to_string();
        expect.assert_eq(&actual);
    }

    fn dbg_check<T: Debug>(actual: T, expect: Expect) {
        let actual = format!("{:?}", actual);
        expect.assert_eq(&actual);
    }

    fn ppr_check<T: Debug>(actual: T, expect: Expect) {
        let actual = format!("{:#?}", actual);
        expect.assert_eq(&actual);
    }

    #[test]
    fn test_concat() {
        let mut s = String::from("ab");
        concat(&mut s, "cde");
        str_check(s, expect!["abcde"]);
    }

    #[test]
    fn test_replace() {
        str_check(
            replace(program, b'(', " ( "),
            expect![" ( begin  ( define r 10)  ( * pi  ( * r r)))"],
        );
        str_check(
            replace(&replace(program, b'(', " ( "), b')', " ) "),
            expect![" ( begin  ( define r 10 )   ( * pi  ( * r r )  )  ) "],
        )
    }

    #[test]
    fn test_split() {
        dbg_check(split("foo  bar", b' '), expect![[r#"["foo", "bar"]"#]]);
        dbg_check(split("foo", b' '), expect![[r#"["foo"]"#]]);
    }

    #[test]
    fn test_lex() {
        /*
         * TODO: Fix the long lines on this function.
         */
        ppr_check(
            lex(expr1),
            expect![[r#"
            [
                "(",
                "+",
                "3",
                "4",
                ")",
            ]"#]],
        );
        ppr_check(
            lex(expr2),
            expect![[r#"
                [
                    "(",
                    "*",
                    "2",
                    "(",
                    "+",
                    "3",
                    "4",
                    ")",
                    ")",
                ]"#]],
        );
        ppr_check(
            lex(program),
            expect![[r#"
                [
                    "(",
                    "begin",
                    "(",
                    "define",
                    "r",
                    "10",
                    ")",
                    "(",
                    "*",
                    "pi",
                    "(",
                    "*",
                    "r",
                    "r",
                    ")",
                    ")",
                    ")",
                ]"#]],
        );
    }

    #[test]
    fn test_atom_read() {
        dbg_check(atom_read("123").unwrap(), expect!["IntLit(123)"]);
        dbg_check(atom_read("123.0").unwrap(), expect!["FltLit(123.0)"]);
        dbg_check(atom_read("123.1").unwrap(), expect!["FltLit(123.1)"]);
        dbg_check(atom_read("foo").unwrap(), expect![[r#"Symbol("foo")"#]]);
    }

    #[test]
    fn test_tokens_read() {
        ppr_check(
            tokens_read(&mut VecDeque::from(lex(expr1))).unwrap(),
            expect![[r#"
                List(
                    [
                        Symbol(
                            "+",
                        ),
                        IntLit(
                            3,
                        ),
                        IntLit(
                            4,
                        ),
                    ],
                )"#]],
        );
        ppr_check(
            tokens_read(&mut VecDeque::from(lex(expr2))).unwrap(),
            expect![[r#"
                List(
                    [
                        Symbol(
                            "*",
                        ),
                        IntLit(
                            2,
                        ),
                        List(
                            [
                                Symbol(
                                    "+",
                                ),
                                IntLit(
                                    3,
                                ),
                                IntLit(
                                    4,
                                ),
                            ],
                        ),
                    ],
                )"#]],
        );
        ppr_check(
            tokens_read(&mut VecDeque::from(lex(program))).unwrap(),
            expect![[r#"
                List(
                    [
                        Symbol(
                            "begin",
                        ),
                        List(
                            [
                                Symbol(
                                    "define",
                                ),
                                Symbol(
                                    "r",
                                ),
                                IntLit(
                                    10,
                                ),
                            ],
                        ),
                        List(
                            [
                                Symbol(
                                    "*",
                                ),
                                Symbol(
                                    "pi",
                                ),
                                List(
                                    [
                                        Symbol(
                                            "*",
                                        ),
                                        Symbol(
                                            "r",
                                        ),
                                        Symbol(
                                            "r",
                                        ),
                                    ],
                                ),
                            ],
                        ),
                    ],
                )"#]],
        );
    }

    #[test]
    fn test_read() {
        ppr_check(
            read(expr1).unwrap(),
            expect![[r#"
                List(
                    [
                        Symbol(
                            "+",
                        ),
                        IntLit(
                            3,
                        ),
                        IntLit(
                            4,
                        ),
                    ],
                )"#]],
        );
        ppr_check(
            read(expr2).unwrap(),
            expect![[r#"
                List(
                    [
                        Symbol(
                            "*",
                        ),
                        IntLit(
                            2,
                        ),
                        List(
                            [
                                Symbol(
                                    "+",
                                ),
                                IntLit(
                                    3,
                                ),
                                IntLit(
                                    4,
                                ),
                            ],
                        ),
                    ],
                )"#]],
        );
        ppr_check(
            read(program).unwrap(),
            expect![[r#"
                List(
                    [
                        Symbol(
                            "begin",
                        ),
                        List(
                            [
                                Symbol(
                                    "define",
                                ),
                                Symbol(
                                    "r",
                                ),
                                IntLit(
                                    10,
                                ),
                            ],
                        ),
                        List(
                            [
                                Symbol(
                                    "*",
                                ),
                                Symbol(
                                    "pi",
                                ),
                                List(
                                    [
                                        Symbol(
                                            "*",
                                        ),
                                        Symbol(
                                            "r",
                                        ),
                                        Symbol(
                                            "r",
                                        ),
                                    ],
                                ),
                            ],
                        ),
                    ],
                )"#]],
        );

        ppr_check(
            read(add_zero).unwrap(),
            expect![[r#"
                List(
                    [
                        Symbol(
                            "+",
                        ),
                        Symbol(
                            "x",
                        ),
                        IntLit(
                            0,
                        ),
                    ],
                )"#]],
        );

        ppr_check(
            read(zero_add).unwrap(),
            expect![[r#"
                List(
                    [
                        Symbol(
                            "+",
                        ),
                        IntLit(
                            0,
                        ),
                        Symbol(
                            "x",
                        ),
                    ],
                )"#]],
        );
    }

    #[test]
    fn test_add_zero_lint() {
        let expr = read(add_zero).unwrap();
        dbg_check(add_zero_lint(expr), expect![[r#"Some("add_zero")"#]]);

        let expr = read(zero_add).unwrap();
        dbg_check(add_zero_lint(expr), expect![[r#"Some("add_zero")"#]])
    }

    #[test]
    fn test_lint() {
        let expr = read(add_zero).unwrap();
        dbg_check(lint(expr), expect![[r#"["add_zero"]"#]]);

        let expr = read(zero_add).unwrap();
        dbg_check(lint(expr), expect![[r#"["add_zero"]"#]])
    }

    /*
     * TODO:
     * - [ ] Add rust or emacs macro for faster testing.
     * - [ ] Faster Emacs expect test updates.
     * - [ ] Add more formal proofs of correctness.
     * - [ ] Improve performance via caching/DoD.
     * - [ ] Write my own trim() implementation?
     * - [ ] Add better error datatype for Result<...> structs.
     * - [ ] Simplify Expr datatype.
     * - [ ] Less verbose pretty printer for Expr.
     * - [ ] Should the atomic expression property be embedded in the type system?
     */
}
