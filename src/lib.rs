#![allow(warnings)]

use std::io;
use std::collections::{VecDeque};
use std::error::{Error};
use std::io::{Read};


const LOGO: &str = r"                          _
                         | |
 ___  ___ ___  _ __ _ __ | |__   ___  __ _ _ __
/ __|/ __/ _ \| '__| '_ \| '_ \ / _ \/ _` | '__|
\__ \ (_| (_) | |  | | | | |_) |  __/ (_| | |
|___/\___\___/|_|  |_| |_|_.__/ \___|\__,_|_|

                                                ";

const BUFSIZE: usize = 1024;

const expr1: &str = "(+ 3 4)";
const expr2: &str = "(* 2 (+ 3 4))";

const add_zero: &str = "(+ x 0)";
const zero_add: &str = "(+ 0 x)";

const mul_one: &str = "(* x 1)"; 
const one_mul: &str = "(* 1 x)";
const mul_fone: &str = "(* x 1.)"; 
const fone_mul: &str = "(* 1. x)";

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

fn extend_bytes(s: &mut String, bs: &[u8]) {
    /*
     * Pre: TODO
     */

    #[cfg(debug_assertions)]
    let n = s.len();
    let m = bs.len();

    let mut i = 0;

    /*
     * Inv: s is the string s[0], ..., s[n - 1], bs[0], ..., bs[m - 1].
     *
     * TODO: This could be made more precise.
     */
    while i < m {
        /*
         * TODO: What's the overheading of converting u8 to char?
         */
        s.push(bs[i] as char);
        i += 1;
    }
    debug_assert!(i == m);

    /*
     * Post: TODO
     */
    debug_assert!(s.len() == n + m);
}

/*
 * TODO: Perhaps write a functional version of this?
 */
fn extend(s: &mut String, t: &str) {
    /*
     * Pre: TODO
     */

    #[cfg(debug_assertions)]
    let n = s.len();
    let m = t.len();

    extend_bytes(s, t.as_bytes());

    /*
     * Post: TODO
     */
    debug_assert!(s.len() == n + m);
}

#[inline(always)]
/*
 * TODO: Extend this to replacing arbitrary strings.
 */
fn replace(s: &str, c: u8, t: &str) -> String {
    /*
     * Pre: TODO
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
            extend(&mut acc, t);
        } else {
            acc.push(bs[i] as char);
        }
        i += 1;
    }

    /*
     * Post: TODO
     */
    acc
}

/*
 * TODO: Extend this to splitting on arbitrary strings.
 */
fn split(s: &str, c: u8) -> Vec<String> {
    /*
     * Pre: TODO
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
     * Post: TODO
     */
    acc
}

fn lex(s: &str) -> Vec<String> {
    /*
     * Pre: TODO
     */
    debug_assert!(s == s.trim());

    /*
     * TODO: Is there a simpler way to write this?
     */
    let ts = split(&replace(&replace(s, b'(', " ( "), b')', " ) "), b' ');

    /*
     * Post: TODO
     */
    ts
}

fn atom_read(s: &str) -> Result<Expr, &'static str> {
    /*
     * Pre: TODO
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
     * Post: TODO
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
     * Pre: TODO
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
     * Post: TODO
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
        Expr::List(xs) => match *xs {
            [Expr::Symbol(ref op), Expr::Symbol(ref x), Expr::IntLit(0)] if op == "+" => { /* TODO: This is a kludge. */
                Some(String::from("add_zero"))
            }
            [Expr::Symbol(ref op), Expr::IntLit(0), Expr::Symbol(ref x)] if op == "+" => {
                Some(String::from("add_zero"))
            }
            _ => None,
        },
        Expr::IntLit(_) | Expr::FltLit(_) | Expr::Symbol(_) => None,
    }
    /*
     * TODO: This procedure is missing postconditions.
     */
}

fn mul_one_lint(x: Expr) -> Option<String> {
    use Expr::*;

    match x {
        List(xs) => match *xs {
            [Symbol(ref op), ref a, ref b] if op == "*" => match (a, b) {
                (Symbol(_), IntLit(1) | FltLit(1.)) | 
                (IntLit(1) | FltLit(1.), Symbol(_)) => Some("mul_one".to_string()),
                _ => None,
            } 
            _ => None,
        }
        IntLit(_) | FltLit(_) | Symbol(_) => None,
    }
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

fn slurp<T: Read>(f: &mut T, buf: &mut String) -> Result<usize, &'static str> {
    /*
     * Pre: TODO
     */

    let mut mybuf: &mut [u8] = &mut [0; BUFSIZE];

    let mut i = 0;

    /*
     * Inv: TODO
     */
    while true {
        match f.read(mybuf) {
            Ok(n) if n > 0 => {
                extend_bytes(buf, &mybuf[i..i + n]);
                i += n;
            },
            Ok(n) => {
                break;
            },
            Err(e) => {
                return Err("slurp: unexpected file read error");
            }
        }
    }

    /*
     * Post: TODO
     */
    Ok(i)
}

pub struct Config {
    pub is_quiet: bool
}

impl Config {
    /*
     * TODO: This procedure needs proper flag handling.
     */
    pub fn build(args: &[String]) -> Result<Config, String> {
        /*
         * Pre: TODO
         */
        if args.len() == 1 {
            Ok(Config {
               is_quiet: false
            })
        } else if args.len() == 2 && args[1] == "-q" {
            Ok(Config {
                is_quiet: true
            })
        } else if args.len() == 2 && args[1] != "-q" {
            Err(format!("sb: invalid option -- {}", args[1]))
        }
        else {
            Err(String::from("too many arguments"))
        }
        /*
         * Post: TODO
         */
    }
}

fn logo() {
    println!("{}", LOGO);
}

pub fn run(config: Config) -> Result<(), Box<dyn Error>> {
    if !config.is_quiet {
        logo();
    }

    let mut stdin = io::stdin();
    let mut buf = String::new();

    slurp(&mut stdin, &mut buf)?;

    println!("hello scornbear");
    println!("program = {}", buf.trim());
    println!("lint = {:?}", lint(read(buf.trim())?));

    Ok(())
}

#[cfg(test)]
mod test {
    use super::*;

    use expect_test::{Expect, expect};

    use std::fs::{File};
    use std::fmt::{Debug};

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
    fn test_extend() {
        let mut s = String::from("ab");
        extend(&mut s, "cde");
        str_check(s, expect!["abcde"]);
    }

    #[test]
    fn test_extend_bytes() {
        let mut s = String::from("ab");
        extend_bytes(&mut s, "cde".as_bytes());
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
    fn test_mul_one_lint() {
        // case: mul one
        let expr = read(mul_one).unwrap(); 
        dbg_check(mul_one_lint(expr), expect![[r#"Some("mul_one")"#]]);

        let expr = read(one_mul).unwrap(); 
        dbg_check(mul_one_lint(expr), expect![[r#"Some("mul_one")"#]]);

        let expr = read(mul_fone).unwrap(); 
        dbg_check(mul_one_lint(expr), expect![[r#"Some("mul_one")"#]]);

        let expr = read(fone_mul).unwrap(); 
        dbg_check(mul_one_lint(expr), expect![[r#"Some("mul_one")"#]]);

        // case: not mul one
        let expr = read(expr2).unwrap(); 
        dbg_check(mul_one_lint(expr), expect!["None"]);
    }

    #[test]
    fn test_lint() {
        let expr = read(add_zero).unwrap();
        dbg_check(lint(expr), expect![[r#"["add_zero"]"#]]);

        let expr = read(zero_add).unwrap();
        dbg_check(lint(expr), expect![[r#"["add_zero"]"#]])
    }

    #[test]
    fn test_slurp() {
        let filename = "data.txt";

        let mut f = File::open(filename).unwrap();
        let mut buf = String::new();

        str_check(slurp(&mut f, &mut buf).unwrap(), expect!["37"]);
        str_check(buf, expect![[r#"
            (begin (define r 10) (* pi (* r r)))
        "#]]);
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
     * - [ ] Rename `scornbear` to `libsb`.
     */
}
