use pest::Parser;
use pest_derive::Parser;

#[derive(Parser)]
#[grammar = "bosco.pest"]
pub struct BoscoParser;

fn main() {
    let program = BoscoParser::parse(Rule::program, "\
            0
            123
            234
            435
    ")
        .expect("parse error");

    for token in program.tokens() {
        println!(">>>>{:?}", token)
    }


    // for literal in program.into_inner() {
    //     match literal.as_rule() {
    //         Rule::int_literal => {
    //             for kind in literal.into_inner() {
    //                 match kind.as_rule() {
    //                     Rule::dec_literal => println!("Found dec: {}", kind.as_str()),
    //                     Rule::hex_literal => println!("Found hex: {}", kind.as_str()),
    //                     Rule::oct_literal => println!("Found dec: {}", kind.as_str()),
    //                     Rule::bin_literal => println!("Found bin: {}", kind.as_str()),
    //                     _ => println!("Found something else {:?}", kind.as_rule())
    //                 }
    //             }
    //
    //         },
    //         Rule::EOI => (),
    //         _ => println!("Found something else {:?}", literal.as_rule())
    //     }
    // }
}
