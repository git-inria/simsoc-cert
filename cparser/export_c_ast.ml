
let parse ic : Cabs.definition list = 
  Parser.file Lexer.initial (Lexer.init "#" ic)

let _ = output_value stdout (parse stdin)
