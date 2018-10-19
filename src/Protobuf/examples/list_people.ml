open Printf
open Addressbook

(* helper functions *)
let list_of_string s =
  List.map (fun c -> Int64.of_int (int_of_char c)) (Batteries.String.to_list s)

let list_to_string l =
  Batteries.String.of_list (List.map (fun x -> char_of_int (Int64.to_int x)) l)

let byteString_of_bytes bytes =
  let n = Bytes.length bytes in
  build_aligned_ByteString n (of_list (list_of_string (Bytes.to_string bytes)))

let bytes =
  let ic = open_in_bin Sys.argv.(1) in
  let len = in_channel_length ic in
  let b = Bytes.create len in
  really_input ic b 0 len;
  close_in ic;
  b

let print_timestamp seconds nanos =
  let t = Core.Time.of_span_since_epoch (Core.Time.Span.create ~sec:(Int64.to_int seconds)
                                           ~ns:(Int64.to_int nanos) ()) in
  printf "%s" (Core.Time.format t "%Y-%m-%dT%H:%M:%SZ" Core.Time.Zone.utc)

let print_last_updated msg =
  match msg with
  | Some last_updated ->
    printf "  Updated: ";
    timestamp_destruct print_timestamp last_updated;
    printf "\n"
  | None -> ()

let print_phone_type ty =
  let s = (match Int64.to_int ty with
      | 0 -> "Mobile"
      | 1 -> "Home"
      | 2 -> "Work"
      | _ -> "Unknown") in
  printf "%s phone" s

let print_phone pn ty =
  printf "  ";
  print_phone_type ty;
  printf " #: %s\n" (list_to_string pn)

let print_person name id email phones last_updated =
  printf "Person ID: %Ld\n" id;
  printf "  Name: %s\n" (list_to_string name);
  if List.length email > 0 then printf "  E-mail address: %s\n" (list_to_string email);
  List.iter (fun p -> phoneNumber_destruct print_phone p) phones;
  print_last_updated last_updated

let print_addressbook ab =
  List.iter (fun p -> person_destruct print_person p) ab

let () =
  match addressBook_decode (byteString_of_bytes bytes) with
  | Some msg -> addressBook_destruct print_addressbook msg
  | None -> printf "Decode failed!!\n"
