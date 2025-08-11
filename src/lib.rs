/* TODO: this needs to be removed! */
#![allow(warnings)]

/* use std::alloc;
use std::mem;
use std::ptr; */

use std::collections::{VecDeque};
use std::error::{Error};
use std::io::{self, Read};

/*
 * === scornbear Design ===
 * The scornbear system is designed first and foremost around *simplicity*.
 *
 * We use the following criteria guide our design:
 * 1) ** Simplicity **
 * 2) Correctness
 * 3) Hackability
 * 4) Performance.
 *
 * TODO: Improve the writing in this message.
 */

/*
 * === scornbear Style ===
 * - "scornbear" should always be written in all lowercase. Never refer to
 *    scornbear as a "system". Always a "program".
 * - Floats with only trailing 0's should be written as "x.". For example, "1.", "3.", "4.".
 * - Convert to String using .to_string() rather than String::from.
 *     Justification: Pipelining is easier with .to_string().
 * - No nested conditionals or nested pattern matching.
 * - We use the OpenBSD commenting style. That is, we use the /* */ delimiters
 *   for comments. All comments should be written in complete sentences with
 *   punctuation.
 *
 *   Here's an example of a comment,
 *   /*
 *    * Your comment goes here.
 *    */.
 *
 *   Small inline comments can be written inline with /*  */.
 */

const LOGO: &str = r"                          _
                         | |
 ___  ___ ___  _ __ _ __ | |__   ___  __ _ _ __
/ __|/ __/ _ \| '__| '_ \| '_ \ / _ \/ _` | '__|
\__ \ (_| (_) | |  | | | | |_) |  __/ (_| | |
|___/\___\___/|_|  |_| |_|_.__/ \___|\__,_|_|

                                                ";

const BUFSIZE: usize = 1024;

#[repr(C)]
struct BVec {
    buf: *mut i32,
    len: usize,
    cap: usize
}

#[repr(C)]
struct BVecDeque; /* TODO */

#[repr(C)]
#[derive(Debug)]
enum Expr {
    IntLit(i32),
    FpLit(f32),
    Symbol(String),
    List(Box<[Expr]>), /* TODO: should be a linked list */
}

/*
 * extend the bytes in s by bs.
 * pre: TODO
 * post: TODO
 */
fn extend_bytes(s: &mut String, bs: &[u8]) {
    #[cfg(debug_assertions)]
    let n = s.len();
    let m = bs.len();

    let mut i = 0;
    /* inv: s is the string s[0], ..., s[n - 1], bs[0], ..., bs[m - 1]. */
    while i < m {
        /* TODO: what's the overheading of converting u8 to char? */
        s.push(bs[i] as char);
        i += 1;
    }
    debug_assert!(i == m);
    debug_assert!(s.len() == n + m);
}

/*
 * extend the string s by t.
 * pre: TODO
 * post: TODO
 */
fn extend(s: &mut String, t: &str) {
    #[cfg(debug_assertions)]
    let n = s.len();
    let m = t.len();

    extend_bytes(s, t.as_bytes());

    debug_assert!(s.len() == n + m);
}

/*
 * replace all instances of c by t in s. 
 * pre:  TODO
 * post: TODO
 */
fn replace(s: &str, c: u8, t: &str) -> String {
    let bs = s.as_bytes();
    let n = bs.len();

    let mut i = 0;
    let mut acc = String::new();
    /* inv: acc is bs[0], ..., bs[i - 1] but for all j st bs[j] == c, acc has the string t inserted instead of c. */
    while i < n {
        if bs[i] == c {
            extend(&mut acc, t);
        } else {
            acc.push(bs[i] as char);
        }
        i += 1;
    }
    acc
}

/*
 * split s on each instance of c.
 * pre: TODO
 * post: TODO
 */
fn split(s: &str, c: u8) -> Vec<String> {
    let bs = s.as_bytes();
    let n = bs.len();

    let mut i = 0;
    let mut acc = vec![];
    /* inv: TODO */
    while i < n {
        if bs[i] == c {
            i += 1;
        } else {
            let mut j = i + 1;
            /* inv: TODO */
            while j < n && bs[j] != c {
                j += 1;
            }
            acc.push(String::from_utf8_lossy(&bs[i..j]).into_owned());
            i = j;
        }
    }
    acc
}

/* 
 * tokenize the string s.
 * pre: TODO
 * post: TODO
 */
fn lex(s: &str) -> Vec<String> {
    debug_assert!(s == s.trim());

    /* TODO: Is there a simpler way to write this? */
    split(&replace(&replace(s, b'(', " ( "), b')', " ) "), b' ')
}

/*
 * parse one atom from the string s.
 * pre: TODO
 * post: TODO
 */
fn atom_read(s: &str) -> Result<Expr, &'static str> {
    debug_assert!(s == s.trim());

    use Expr::{FpLit, IntLit, Symbol};

    /* TODO: This is really ugly. */
    match s.parse::<i32>() {
        Ok(n) => Ok(IntLit(n)),
        Err(_) => match s.parse::<f32>() {
            Ok(x) => Ok(FpLit(x)),
            Err(_) => Ok(Symbol(s.to_string())),
        },
    }
}

/*
 * parse the given list of tokens.
 * pre: TODO
 * post: TODO
 * TODO: How the hell was this algorithm derived?
 * TODO: I need to transform this into an iterative procedure using a stack. I
 *       don't want mutable references.
 */
fn tokens_read(ts: &mut VecDeque<String>) -> Result<Expr, &'static str> {
    /*
     * TODO: what is as_str() doing?
     * TODO: this code is really ugly.
     */
    match ts.pop_front() {
        Some(t) => match t.as_str() {
            "(" => {
                /* TODO: why is this block correct? */
                let mut xs = vec![];
                /* inv: TODO */
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
    }
}

/*
 * parse the string s into an expression.
 * pre: TODO
 * post: TODO
 */
fn read(s: &str) -> Result<Expr, &'static str> {
    tokens_read(&mut VecDeque::from(lex(s)))
}

/*
 * TODO
 * pre: TODO
 * post: TODO
 */
fn add_zero_lint(x: Expr) -> Option<String> {
    use Expr::{FpLit, IntLit, List, Symbol};

    match x {
        List(xs) => match xs.as_ref() {
            [Symbol(op), Symbol(x), IntLit(0)] if op == "+" => Some("add_zero".to_string()),
            [Symbol(op), Symbol(x), FltLit(0.)] if op == "+" => Some("add_zero".to_string()),
            [Symbol(op), IntLit(0), Symbol(x)] if op == "+" => Some("add_zero".to_string()),
            [Symbol(op), FltLit(0.), Symbol(x)] if op == "+" => Some("add_zero".to_string()),
            _ => None,
        },
        IntLit(_) | FpLit(_) | Symbol(_) => None,
    }
}

/*
 * TODO
 * pre: TODO
 * post: TODO
 */
fn mul_one_lint(x: Expr) -> Option<String> {
    use Expr::{FpLit, IntLit, List, Symbol};

    match x {
        List(xs) => match xs.as_ref() {
            [Symbol(op), Symbol(x), IntLit(1)] if op == "*" => Some("mul_one".to_string()),
            [Symbol(op), Symbol(x), FpLit(1.)] if op == "*" => Some("mul_one".to_string()),
            [Symbol(op), IntLit(1), Symbol(x)] if op == "*" => Some("mul_one".to_string()),
            [Symbol(op), FpLit(1.), Symbol(x)] if op == "*" => Some("mul_one".to_string()),
            _ => None,
        },
        IntLit(_) | FpLit(_) | Symbol(_) => None,
    }
}

/*
 * TODO
 * pre: TODO
 * post: TODO
 */
fn lint(x: Expr) -> Vec<String> {
    match add_zero_lint(x) {
        None => vec![],
        Some(s) => vec![s],
    }
}

/* TODO */
fn raise(x: Expr) -> Expr {
    todo!()
}

/*
 * slurps TODO
 * pre: TODO
 * post: TODO
 */
fn slurp<T: Read>(f: &mut T, buf: &mut String) -> Result<usize, &'static str> {
    let mut mybuf: &mut [u8] = &mut [0; BUFSIZE];
    let mut i = 0;
    /* inv: TODO */
    while true {
        match f.read(mybuf) {
            Ok(n) if n > 0 => {
                extend_bytes(buf, &mybuf[i..i + n]);
                i += n;
            }
            Ok(n) => {
                break;
            }
            Err(e) => {
                return Err("slurp: unexpected file read error");
            }
        }
    }
    Ok(i)
}

#[repr(C)]
pub struct Config {
    pub is_quiet: bool,
}

impl Config {
    /* 
     * builds TODO
     * pre: TODO
     * post: TODO
     * TODO: this functions needs proper flag handling. 
     */
    pub fn build(args: &[String]) -> Result<Config, String> {
        if args.len() == 1 {
            Ok(Config { is_quiet: false })
        } else if args.len() == 2 && args[1] == "-q" {
            Ok(Config { is_quiet: true })
        } else if args.len() == 2 && args[1] != "-q" {
            Err(format!("sb: invalid option -- {}", args[1]))
        } else {
            Err(String::from("too many arguments"))
        }
    }
}

/* prints TODO
 * pre: TODO
 * post: TODO
 */
fn logo() {
    println!("{}", LOGO);
}

/*
 * runs TODO
 * pre: TODO
 * post: TODO
 */
pub fn run(config: Config) -> Result<(), Box<dyn Error>> {
    /*
     * Pre: TODO
     */
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
    /*
     * Post: TODO
     */
}

#[cfg(test)]
mod test {
    use std::fmt::Debug;
    use std::fs::File;

    use expect_test::{Expect, expect};

    use super::*;

    const expr1: &str = "(+ 3 4)";
    const expr2: &str = "(* 2 (+ 3 4))";

    const add_zero: &str = "(+ x 0)";
    const zero_add: &str = "(+ 0 x)";
    const add_fzero: &str = "(+ x 0.)"; 
    const fzero_add: &str = "(+ 0. x)"; 

    const mul_one: &str = "(* x 1)";
    const one_mul: &str = "(* 1 x)";
    const mul_fone: &str = "(* x 1.)";
    const fone_mul: &str = "(* 1. x)";

    const program: &str = "(begin (define r 10) (* pi (* r r)))";

    const neg1: Expr = Expr::IntLit(-1);

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
        /* TODO: fix the long lines on this function. */
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
        dbg_check(atom_read("123.0").unwrap(), expect!["FpLit(123.0)"]);
        dbg_check(atom_read("123.1").unwrap(), expect!["FpLit(123.1)"]);
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
        dbg_check(add_zero_lint(expr), expect![[r#"Some("add_zero")"#]]);

        let expr = read(add_fzero).unwrap(); 
        dbg_check(add_zero_lint(expr), expect![[r#"Some("add_zero")"#]]);

        let expr = read(fzero_add).unwrap(); 
        dbg_check(add_zero_lint(expr), expect![[r#"Some("add_zero")"#]]);
    }

    #[test]
    fn test_mul_one_lint() {
        /* case: mul one */
        let expr = read(mul_one).unwrap();
        dbg_check(mul_one_lint(expr), expect![[r#"Some("mul_one")"#]]);

        let expr = read(one_mul).unwrap();
        dbg_check(mul_one_lint(expr), expect![[r#"Some("mul_one")"#]]);

        let expr = read(mul_fone).unwrap();
        dbg_check(mul_one_lint(expr), expect![[r#"Some("mul_one")"#]]);

        let expr = read(fone_mul).unwrap();
        dbg_check(mul_one_lint(expr), expect![[r#"Some("mul_one")"#]]);

        /* case: none */
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
        let filename = "program.txt";

        let mut f = File::open(filename).unwrap();
        let mut buf = String::new();

        str_check(slurp(&mut f, &mut buf).unwrap(), expect!["37"]);
        str_check(
            buf,
            expect![[r#"
            (begin (define r 10) (* pi (* r r)))
        "#]],
        );
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
     * - [ ] Add float arms for zero_lint.
     * - [ ] Reify Mul, Add to Expr (then simplify corresponds rules).
     * - [ ] Convert String::from to .to_string()
     * - [ ] Add Rule enum and convert corresponding lints.
     * - [ ] Add property-based tests.
     * - [ ] Move test expressions into mod test.
     */
}
