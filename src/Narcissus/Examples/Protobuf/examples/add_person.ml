open Printf
open Addressbook

let list_of_string s =
  List.map (fun c -> Int64.of_int (int_of_char c)) (Batteries.String.to_list s)

let list_to_string l =
  Batteries.String.of_list (List.map (fun x -> char_of_int (Int64.to_int x)) l)

let byteString_of_bytes bytes =
  let n = Bytes.length bytes in
  build_aligned_ByteString n (of_list (list_of_string (Bytes.to_string bytes)))

let byteString_to_bytes bs =
  Bytes.of_string (list_to_string (to_list (numBytes bs) (byteString0 bs)))

let bytes =
  try
    let ic = open_in_bin Sys.argv.(1) in
    let len = in_channel_length ic in
    let b = Bytes.create len in
    really_input ic b 0 len;
    close_in ic;
    Some b
  with Sys_error e ->
    printf "%s: File not found. Creating new file.\n" Sys.argv.(1);
    None

let ab =
  match bytes with
  | Some bytes ->
    (match addressBook_decode (byteString_of_bytes bytes) with
     | Some msg -> addressBook_destruct (fun ab -> Some ab) msg
     | None -> None)
  | None -> Some []

let rec read_phones () =
  printf "Enter a phone number (or leave blank to finish): ";
  let phone = String.trim (read_line ()) in
  if String.length phone > 0 then
    (printf "Enter phone type: ";
     let ptype = read_int () in
     (phoneNumber_construct (list_of_string phone) ptype) :: read_phones ())
  else []

let read_timestamp =
  (* Precision is only in seconds. *)
  timestamp_construct (int_of_float (Unix.time ())) 0

let read_person =
  printf "Enter person ID number: ";
  let id = read_int () in
  printf "Enter name: ";
  let name = String.trim (read_line ()) in
  printf "Enter email address (blank for none): ";
  let email = String.trim (read_line ()) in
  let phones = read_phones () in
  let last_updated = read_timestamp in
  person_construct (list_of_string name) id (list_of_string email) phones (Some last_updated)

let () =
  match ab with
  | Some ab ->
    let bs = addressBook_encode (addressBook_construct (ab@[read_person])) in
    let bytes = byteString_to_bytes bs in
    let oc = open_out_bin Sys.argv.(1) in
    output_bytes oc bytes;
    close_out oc
  | None -> printf "Parse failed!!\n"
