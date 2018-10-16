open Testall
open Printf
open BatIO

let list_of_string s =
  List.map (fun c -> Int64.of_int (int_of_char c)) (Batteries.String.to_list s)

let list_to_string l =
  Batteries.String.of_list (List.map (fun x -> char_of_int (Int64.to_int x)) l)

let byteString_of_string s =
  let n = String.length s in
  build_aligned_ByteString n (of_list (list_of_string s))

let byteString_to_string bs =
  list_to_string (to_list (numBytes bs) (byteString0 bs))

let main bs =
  match testall_decode bs with
  | Some msg -> Some (testall_encode msg)
  | None -> None

let () =
  let bs = byteString_of_string (read_all stdin) in
  match main bs with
  | Some bs -> nwrite stdout (byteString_to_string bs)
  | None -> exit 1
