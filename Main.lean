import HaskellSpec

import HaskellSpec.Lexer.Haskell.Combined

def process_file(filepath : System.FilePath) : IO Unit := do
  IO.println s!"Processing file {filepath}"
  let file_content ← IO.FS.readFile filepath
  let tokens := lex_haskell file_content
  let printed_tokens := reprStr tokens
  IO.println s!"{printed_tokens}"



def main(args : List String): IO Unit :=
  match args with
  | [fp] => process_file fp
  | _ => IO.println s!"Call the executable with exactly one argument"
