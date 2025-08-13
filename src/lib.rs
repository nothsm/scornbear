/* TODO: this needs to be removed! */
#![allow(warnings)]
#![crate_name = "libsb"]
#![crate_type = "lib"]

use std::fmt::{self, Display};

use std::alloc::{self, Layout};
use std::mem;
use std::ptr;

use std::collections::VecDeque;
use std::error::Error;
use std::io::{self, Read};

/*
 * === scornbear design ===
 * the scornbear program is designed first and foremost around *simplicity*.
 *
 * we use the following criteria guide our design:
 * 1) ** simplicity **
 * 2) correctness
 * 3) hackability
 * 4) performance.
 *
 * TODO: improve the writing in this message.
 */

/*
 * === scornbear style ===
 * - in documentation, "scornbear" should always be written in all lowercase.
 *     - why: to exec scornbear, you type "scornbear" into your tty, not
 *            "Scornbear."
 * -  never refer to scornbear as a "system". always a "program".
 *     - why: a program is something you exec. a system is a collection of programs.
 *            then, scornbear is something you exec (and thus, is a program).
 * - floats with only trailing 0's should be written as "x.", not "x.0".
 *     - ex: write "1." over "1.0".
 *     - ex: write "3." over "3.0".
 *     - why: it is more concise to drop trailing zeroes.
 * - convert to String using .to_string() rather than String::from.
 *     - why: pipelining is easier with .to_string().
 * - no nested conditionals or nested pattern matching.
 *     - why: nested conditional logic is very complex. its hard to read.
 *            it's hard to reason about.
 * - use the openbsd commenting style.
 *     - ex: read the code.
 *     - why: openbsd code is beautiful.
 * - all comments should be written in complete sentences with punctuation.
 *     - why: this is left as an exercise for the reader.
 * - every should function should be documented with at least:
 *   (i)   one sentence describing what it does,
 *   (ii)  one sentence describing its preconditions,
 *   (iii) one sentence describing its postconditions.
 *     - ex: read the code.
 *     - why: TODO
 * - every loop should be documented with at least a one-sentence invariant.
 *     - ex: read the code.
 *     - why: TODO
 */

const LOGO: &str = r"                          _
                         | |
 ___  ___ ___  _ __ _ __ | |__   ___  __ _ _ __
/ __|/ __/ _ \| '__| '_ \| '_ \ / _ \/ _` | '__|
\__ \ (_| (_) | |  | | | | |_) |  __/ (_| | |
|___/\___\___/|_|  |_| |_|_.__/ \___|\__,_|_|

                                                ";
const BUFSIZE: usize = 1024;
const BVEC_SIZE: usize = 4;

/*
 * round up the usize x to the nearest multiple of the usize y.
 * pre: TODO
 * post: TODO
 * TODO: needs more rigorous understanding + testing.
 * TODO: perhaps use some bitwise tricks here?
 */
fn round_up(x: usize, y: usize) -> usize {
    if y == 0 {
        0
    } else if x % y == 0 {
        x
    } else {
        debug_assert!(y > 0);
        ((x / y) + 1) * y
    }
}

/*
 * represents a (scorn)bear vector.
 * af: obj = TODO
 * ri: self.len < self.cap, TODO
 */
#[repr(C)]
#[derive(Debug)]
struct BVec {
    ptr: *mut i32,
    len: usize,
    cap: usize,
}

/*
 * check the bvec rep inv for the bvec xs.
 * pre: TODO
 * post: TODO
 */
fn bvec_check_rep(xs: &BVec) {
    debug_assert!(xs.len < xs.cap);
}

/*
 * construct a new bvec.
 * pre: TODO
 * post: TODO
 * TODO: properly handle layout errors.
 * TODO: lazily allocate bvec. this is inefficient.
 * TODO: make this function nicer.
 * TODO: perhaps write my own Layout functions.
 * TODO: perhaps use NonNull<i32> for ptr?
 */
fn bvec_new() -> BVec {
    let layout = Layout::array::<i32>(BVEC_SIZE).unwrap();
    if layout.size() == 0 {
        alloc::handle_alloc_error(layout);
    }
    assert!(layout.size() > 0);

    let ptr = unsafe { alloc::alloc_zeroed(layout) } as *mut i32;
    if ptr.is_null() {
        alloc::handle_alloc_error(layout);
    }
    let len = 0;
    let cap = BVEC_SIZE;

    let xs = BVec { ptr, len, cap };
    bvec_check_rep(&xs);

    xs
}

/*
 * get the length of the bvec xs.
 * pre: TODO
 * post: TODO
 * TODO: add tests.
 */
fn bvec_len(xs: &BVec) -> usize {
    bvec_check_rep(xs);
    xs.len
}

/*
 * return true if the bvec xs is empty (length == 0), else false.
 * pre: TODO
 * post: TODO
 */
fn bvec_is_empty(xs: &BVec) -> bool {
    bvec_check_rep(xs);
    bvec_len(xs) == 0
}

/*
 * get the capacity of the buffer allocated for the bvec xs.
 * pre: TODO
 * post: TODO
 */
fn bvec_capacity(xs: &BVec) -> usize {
    bvec_check_rep(xs);
    xs.cap
}

/*
 * get a raw mutable pointer to the bvec xs's buffer.
 * pre: TODO
 * post: TODO
 * TODO: this should take in &mut BVec, not &BVec.
 * TODO: add tests.
 * TODO: I think this is super unsafe. I should add tests or checks.
 */
fn bvec_as_mut_ptr(xs: &BVec) -> *mut i32 {
    bvec_check_rep(xs);
    xs.ptr
}

/*
 * get the element at index i in the bvec xs.
 * pre: TODO
 * post: TODO
 * TODO: how do I write my own pointer arithmetic implementation?
 * TODO: don't use as_mut_ptr() (use const version).
 * TODO: add tests.
 * TODO: should I use ptr::read here?
 */
fn bvec_get(xs: &BVec, i: usize) -> i32 {
    debug_assert!(i < bvec_len(xs));
    bvec_check_rep(xs);

    let ptr = bvec_as_mut_ptr(xs);
    let count = i;

    /* check preconditions for ptr.add */
    let offset = count * mem::size_of::<i32>();
    let max_isize = isize::MAX.try_into().unwrap();
    debug_assert!(offset < max_isize); /* TODO: should this be a <=? */
    if offset > 0 { /* TODO: check the other precondition for pointer::add. */ }

    unsafe { *ptr.add(count) } /* TODO: what are the preconditions for dereferencing raw ptrs? */
}

/*
 * set the element at index i to value x in the bvec xs.
 * pre: TODO
 * post: TODO
 * TODO: should I use ptr::write here?
 * TODO: add tests.
 * TODO: check or improve the clarity of this comment.
 * TODO: DONT USE THIS YET! it's for internal use only.
 */
fn bvec_set(xs: &mut BVec, i: usize, x: i32) {
    /*  TODO: this should be true, but not checking it makes implementation easier  */
    /*  debug_assert!(i < bvec_len(xs)); */
    debug_assert!(i < bvec_capacity(xs));
    bvec_check_rep(xs);

    let ptr = bvec_as_mut_ptr(xs);
    let count = i;

    /* check preconditions for ptr.add. */
    let offset = count * mem::size_of::<i32>();
    let max_isize = isize::MAX.try_into().unwrap();
    assert!(offset < max_isize); /* TODO: should this be <=? */
    if offset > 0 { /* TODO: check the other precondition for pointer::add. */ }

    unsafe { *ptr.add(count) = x }; /* TODO: there MUST be some precondition for assigning to raw ptrs... */
    bvec_check_rep(xs);
}

/*
 * free the memory allocated for the bvec xs.
 * pre: TODO
 * post: TODO
 * TODO: safer Layout::array result handling.
 */
fn bvec_free(xs: &mut BVec) {
    bvec_check_rep(&xs);

    let ptr = bvec_as_mut_ptr(&xs) as *mut u8;
    let layout = Layout::array::<i32>(bvec_capacity(&xs)).unwrap();
    unsafe { alloc::dealloc(ptr, layout) }; /* I am not checking this at all LOL. */
}

/*
 * convert the bvec xs to a (debug) string
 * pre: TODO
 * post: TODO
 * TODO: write my own String implementation.
 * TODO: use proper rust traits.
 * TODO: use a proper formatter.
 * TODO: use bvec selectors rather than dereferencing directly into the bvec struct?
 */
fn bvec_dbg(xs: &BVec) -> String {
    bvec_check_rep(xs);

    String::from(format!("BVec {{ len: {}, cap: {} }}", xs.len, xs.cap)) /* disgusting and bloated. */
}

/*
 * convert the bvec xs to a string.
 * pre: TODO
 * post: TODO
 * TODO: write my own String implementation.
 * TODO: write my own i32 -> char implementation.
 * TODO: use a safe i32 -> char implementation.
 * TODO: use proper rust traits.
 * TODO: test this.
 */
fn bvec_show(xs: &BVec) -> String {
    bvec_check_rep(xs);

    if bvec_is_empty(xs) {
        return String::from("[]");
    }

    let mut i = 0;
    let mut acc = String::new();
    acc.push('[');

    /* TODO: use early return for empty case. */
    /* inv: TODO */
    while i < bvec_len(xs) - 1 {
        let x = bvec_get(xs, i);
        acc.push_str(&x.to_string());
        acc.push(' ');
        i += 1;
    }
    debug_assert!(i == bvec_len(xs) - 1);

    let x = bvec_get(xs, i);
    acc.push_str(&x.to_string());
    acc.push(']');
    acc
}

/*
 * append the element x to the back of the bvec xs.
 * pre: TODO
 * post: TODO
 * TODO: proper Layout error handling.
 * TODO: more efficient resizing.
 * TODO: this could be more elegant.
 */
fn bvec_push(xs: &mut BVec, x: i32) {
    bvec_check_rep(xs);

    let len = bvec_len(xs);
    let cap = bvec_capacity(xs);

    let new_len = bvec_len(xs) + 1;
    bvec_set(xs, len, x);
    if new_len == cap {
        let new_cap = 2 * cap;

        let ptr = bvec_as_mut_ptr(xs) as *mut u8;
        let layout = Layout::array::<i32>(cap).unwrap();
        let new_size = Layout::array::<i32>(new_cap).unwrap().size();

        /* check realloc preconditions. */
        let max_isize = isize::MAX.try_into().unwrap();
        if new_size == 0 {
            alloc::handle_alloc_error(layout);
        }
        if round_up(new_size, layout.align()) > max_isize {
            alloc::handle_alloc_error(layout);
        }
        debug_assert!(new_size > 0);
        debug_assert!(round_up(new_size, layout.align()) <= max_isize);

        let new_ptr = unsafe { alloc::realloc(ptr, layout, new_size) } as *mut i32;
        if new_ptr.is_null() {
            alloc::handle_alloc_error(layout);
        }

        xs.ptr = new_ptr;
        xs.cap = new_cap;
    }
    xs.len = new_len;
    bvec_check_rep(xs);
}

impl Drop for BVec {
    fn drop(&mut self) {
        bvec_free(self);
    }
}

impl Display for BVec {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", bvec_show(self))
    }
}

/* TODO */
#[repr(C)]
struct BString; /* bear (growable, heap-allocated) string */

/* TODO */
struct BBox; /* bear box */

/* TODO */
#[repr(C)]
struct BVecDeque; /* bear vecdeque */

#[repr(C, u8)]
#[derive(Debug)]
enum Expr {
    IntLit(i32),
    FpLit(f32),
    Symbol(String),
    List(Box<[Expr]>), /* TODO: should be a linked list */
}

/*
 * append bytes bs to the string s.
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
 * append str t to the string s.
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

    /* TODO: this is really ugly. */
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
 * TODO: how the hell was this algorithm derived?
 * TODO: make this function iterative, using a stack.
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
            [Symbol(op), Symbol(x), FpLit(0.)] if op == "+" => Some("add_zero".to_string()),
            [Symbol(op), IntLit(0), Symbol(x)] if op == "+" => Some("add_zero".to_string()),
            [Symbol(op), FpLit(0.), Symbol(x)] if op == "+" => Some("add_zero".to_string()),
            _ => None,
        },
        IntLit(_) | FpLit(_) | Symbol(_) => None,
    }
}

/*
 * lints TODO
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
 * lints TODO
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
    fn test_round_up() {
        str_check(round_up(0, 1), expect!["0"]);
        str_check(round_up(0, 2), expect!["0"]);
        str_check(round_up(1, 5), expect!["5"]);
        str_check(round_up(1, 0), expect!["0"]);
        str_check(round_up(2, 0), expect!["0"]);
        str_check(round_up(7, 1), expect!["7"]);
        str_check(round_up(7, 2), expect!["8"]);
        str_check(round_up(7, 3), expect!["9"]);
        str_check(round_up(7, 4), expect!["8"]);
        str_check(round_up(7, 5), expect!["10"]);
        str_check(round_up(7, 14), expect!["14"]);
        str_check(round_up(7, 15), expect!["15"]);
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
        let filename = "data/program.txt";

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

    #[test]
    fn test_bvec_new() {
        let mut xs = bvec_new();

        str_check(&xs, expect!["[]"]);
        str_check(bvec_dbg(&xs), expect!["BVec { len: 0, cap: 4 }"]);
        str_check(bvec_len(&xs), expect!["0"]);
        str_check(bvec_is_empty(&xs), expect!["true"]);
        str_check(bvec_capacity(&xs), expect!["4"]);
    }

    #[test]
    fn test_bvec_push() {
        let mut xs = bvec_new();
        str_check(&xs, expect!["[]"]);
        str_check(bvec_dbg(&xs), expect!["BVec { len: 0, cap: 4 }"]);
        str_check(bvec_len(&xs), expect!["0"]);
        str_check(bvec_is_empty(&xs), expect!["true"]);
        str_check(bvec_capacity(&xs), expect!["4"]);

        bvec_push(&mut xs, 1);
        str_check(&xs, expect!["[1]"]);
        str_check(bvec_dbg(&xs), expect!["BVec { len: 1, cap: 4 }"]);
        str_check(bvec_len(&xs), expect!["1"]);
        str_check(bvec_is_empty(&xs), expect!["false"]);
        str_check(bvec_capacity(&xs), expect!["4"]);

        bvec_push(&mut xs, 2);
        str_check(&xs, expect!["[1 2]"]);
        str_check(bvec_dbg(&xs), expect!["BVec { len: 2, cap: 4 }"]);
        str_check(bvec_len(&xs), expect!["2"]);
        str_check(bvec_is_empty(&xs), expect!["false"]);
        str_check(bvec_capacity(&xs), expect!["4"]);

        bvec_push(&mut xs, 3);
        str_check(&xs, expect!["[1 2 3]"]);
        str_check(bvec_dbg(&xs), expect!["BVec { len: 3, cap: 4 }"]);
        str_check(bvec_len(&xs), expect!["3"]);
        str_check(bvec_is_empty(&xs), expect!["false"]);
        str_check(bvec_capacity(&xs), expect!["4"]);

        bvec_push(&mut xs, 4);
        str_check(&xs, expect!["[1 2 3 4]"]);
        str_check(bvec_dbg(&xs), expect!["BVec { len: 4, cap: 8 }"]);
        str_check(bvec_len(&xs), expect!["4"]);
        str_check(bvec_is_empty(&xs), expect!["false"]);
        str_check(bvec_capacity(&xs), expect!["8"]);

        bvec_push(&mut xs, 5);
        str_check(&xs, expect!["[1 2 3 4 5]"]);
        str_check(bvec_dbg(&xs), expect!["BVec { len: 5, cap: 8 }"]);
        str_check(bvec_len(&xs), expect!["5"]);
        str_check(bvec_is_empty(&xs), expect!["false"]);
        str_check(bvec_capacity(&xs), expect!["8"]);

        bvec_push(&mut xs, 6);
        str_check(&xs, expect!["[1 2 3 4 5 6]"]);
        str_check(bvec_dbg(&xs), expect!["BVec { len: 6, cap: 8 }"]);
        str_check(bvec_len(&xs), expect!["6"]);
        str_check(bvec_is_empty(&xs), expect!["false"]);
        str_check(bvec_capacity(&xs), expect!["8"]);

        bvec_push(&mut xs, 7);
        str_check(&xs, expect!["[1 2 3 4 5 6 7]"]);
        str_check(bvec_dbg(&xs), expect!["BVec { len: 7, cap: 8 }"]);
        str_check(bvec_len(&xs), expect!["7"]);
        str_check(bvec_is_empty(&xs), expect!["false"]);
        str_check(bvec_capacity(&xs), expect!["8"]);

        bvec_push(&mut xs, 8);
        str_check(&xs, expect!["[1 2 3 4 5 6 7 8]"]);
        str_check(bvec_dbg(&xs), expect!["BVec { len: 8, cap: 16 }"]);
        str_check(bvec_len(&xs), expect!["8"]);
        str_check(bvec_is_empty(&xs), expect!["false"]);
        str_check(bvec_capacity(&xs), expect!["16"]);

        bvec_push(&mut xs, 9);
        str_check(&xs, expect!["[1 2 3 4 5 6 7 8 9]"]);
        str_check(bvec_dbg(&xs), expect!["BVec { len: 9, cap: 16 }"]);
        str_check(bvec_len(&xs), expect!["9"]);
        str_check(bvec_is_empty(&xs), expect!["false"]);
        str_check(bvec_capacity(&xs), expect!["16"]);

        bvec_push(&mut xs, -1);
        str_check(&xs, expect!["[1 2 3 4 5 6 7 8 9 -1]"]);
        str_check(bvec_dbg(&xs), expect!["BVec { len: 10, cap: 16 }"]);
        str_check(bvec_len(&xs), expect!["10"]);
        str_check(bvec_is_empty(&xs), expect!["false"]);
        str_check(bvec_capacity(&xs), expect!["16"]);

        bvec_push(&mut xs, 21);
        str_check(&xs, expect!["[1 2 3 4 5 6 7 8 9 -1 21]"]);
        str_check(bvec_dbg(&xs), expect!["BVec { len: 11, cap: 16 }"]);
        str_check(bvec_len(&xs), expect!["11"]);
        str_check(bvec_is_empty(&xs), expect!["false"]);
        str_check(bvec_capacity(&xs), expect!["16"]);

        bvec_push(&mut xs, -32);
        str_check(&xs, expect!["[1 2 3 4 5 6 7 8 9 -1 21 -32]"]);
        str_check(bvec_dbg(&xs), expect!["BVec { len: 12, cap: 16 }"]);
        str_check(bvec_len(&xs), expect!["12"]);
        str_check(bvec_is_empty(&xs), expect!["false"]);
        str_check(bvec_capacity(&xs), expect!["16"]);

        bvec_push(&mut xs, 43);
        str_check(&xs, expect!["[1 2 3 4 5 6 7 8 9 -1 21 -32 43]"]);
        str_check(bvec_dbg(&xs), expect!["BVec { len: 13, cap: 16 }"]);
        str_check(bvec_len(&xs), expect!["13"]);
        str_check(bvec_is_empty(&xs), expect!["false"]);
        str_check(bvec_capacity(&xs), expect!["16"]);

        bvec_push(&mut xs, -54);
        str_check(&xs, expect!["[1 2 3 4 5 6 7 8 9 -1 21 -32 43 -54]"]);
        str_check(bvec_dbg(&xs), expect!["BVec { len: 14, cap: 16 }"]);
        str_check(bvec_len(&xs), expect!["14"]);
        str_check(bvec_is_empty(&xs), expect!["false"]);
        str_check(bvec_capacity(&xs), expect!["16"]);

        bvec_push(&mut xs, 65);
        str_check(&xs, expect!["[1 2 3 4 5 6 7 8 9 -1 21 -32 43 -54 65]"]);
        str_check(bvec_dbg(&xs), expect!["BVec { len: 15, cap: 16 }"]);
        str_check(bvec_len(&xs), expect!["15"]);
        str_check(bvec_is_empty(&xs), expect!["false"]);
        str_check(bvec_capacity(&xs), expect!["16"]);

        bvec_push(&mut xs, -76);
        str_check(&xs, expect!["[1 2 3 4 5 6 7 8 9 -1 21 -32 43 -54 65 -76]"]);
        str_check(bvec_dbg(&xs), expect!["BVec { len: 16, cap: 32 }"]);
        str_check(bvec_len(&xs), expect!["16"]);
        str_check(bvec_is_empty(&xs), expect!["false"]);
        str_check(bvec_capacity(&xs), expect!["32"]);
    }

    /*
     * TODO:
     * - [ ] write my own expect test library.
     * - [ ] add rust or emacs macro for faster testing.
     * - [ ] faster emacs expect test updates.
     * - [ ] add more formal proofs of correctness.
     * - [ ] improve performance via caching/DoD.
     * - [ ] write my own trim() implementation?
     * - [ ] add better error datatype for Result<...> structs.
     * - [ ] simplify Expr datatype.
     * - [ ] less verbose pretty printer for Expr.
     * - [ ] should the atomic expression property be embedded in the type system?
     * - [ ] add Mul, Add to Expr (then simplify corresponds rules).
     * - [ ] add Rule trait and convert corresponding lints.
     * - [ ] add property-based tests.
     * - [ ] rename tests st prefixes restrict.
     * - [ ] should i check ri before or after pre-/post-conditions?
     * - [ ] add more unit tests for bvec.
     * - [ ] check I'm actually satisfying all the unsafe block preconditions.
     * - [ ] I should be free'ing BVec on panics
     */
}
