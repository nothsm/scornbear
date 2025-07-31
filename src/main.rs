/*
 * TODO: Remove this!!
 */

use std::env;
use std::process;

use scornbear::{Config};

fn usage() {
    eprintln!("usage: sb [-q]");
}

fn main() {
    let args: Vec<String> = env::args().collect();

    let config = Config::build(&args).unwrap_or_else(|err| {
        eprintln!("{}", err);
        usage();
        process::exit(1);
    });

    if let Err(e) = scornbear::run(config) {
        eprintln!("ls: internal error -- {}", e);
        process::exit(1);
    }
}
