#![crate_type = "bin"]
#![crate_name = "sb"]

use std::env;
use std::process;

// extern crate libsb; /* TODO: how do i configure rustc so this isn't necessary? */

use libsb::Config;

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

    if let Err(e) = libsb::run(config) {
        eprintln!("sb: internal error -- {}", e);
        process::exit(1);
    }
}
