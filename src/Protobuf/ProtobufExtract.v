Require Import
        NArith
        ExtrOcamlBasic
        ExtrOcamlNatInt
        ExtrOcamlString.

Require Import
        Fiat.QueryStructure.Specification.Representation.Notations
        Fiat.QueryStructure.Specification.Representation.Heading
        Fiat.QueryStructure.Specification.Representation.Tuple
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Common.WordFacts
        Fiat.Narcissus.BinLib.Core
        Fiat.Narcissus.BinLib.AlignedMonads
        Fiat.Narcissus.Formats.WordOpt
        Fiat.Narcissus.Formats.VarintOpt
        Fiat.Narcissus.Stores.EmptyStore.

Require Export
        Fiat.Protobuf.ProtobufSpec
        Fiat.Protobuf.ProtobufEncoder.

Definition PB_Message_encode_impl desc (msg : PB_Message_denote desc) :=
  let (bs, _) := PB_Message_encode desc msg in
  bs.

Definition PB_Message_decode_impl desc bs :=
  match PB_Message_decode desc bs tt with
  | Some (msg, _, _) => Some msg
  | None => None
  end.

Notation "( ty , name , tag )" :=
  (Build_PB_Field ty name tag)
  : Protobuf_scope.

Notation "[ fld1 ; .. ; fldn ]" :=
  (Build_PB_Message (@Vector.cons _ fld1 _ .. (Vector.cons _ fldn _ (Vector.nil _)) ..))
  : Protobuf_scope.

Delimit Scope Protobuf_scope with protobuf.

Extraction Inline DecodeBindOpt2.
Extraction Inline If_Opt_Then_Else.
Extract Constant whd => "(fun _ w -> ((Int64.logand Int64.one w) = Int64.one))".
Extract Constant wtl => "(fun _ w -> (Int64.shift_right_logical w 1))".
Extract Constant wplus => "(fun _ w w' -> Int64.add w w')".
Extract Constant wmult => "(fun _ w w' -> Int64.mul w w')".
Extract Constant wminus => "(fun _ w w' -> Int64.max (Int64.zero) (Int64.sub w w'))".
Extract Constant weq => "(fun _ w w' -> w = w')".
Extract Constant weqb => "(fun _ w w' -> w = w')".
Extract Constant wlt => "(fun _ w w' -> w < w')".
Extract Constant wlt_dec => "(fun _ w w' -> w < w')".
Extract Constant wand => "(fun _ w w' -> Int64.logand w w')".
Extract Constant wor => "(fun _ w w' -> Int64.logor w w')".
Extract Constant wnot => "(fun _ w -> Int64.lognot w)".
Extract Constant wneg => "(fun _ w w' -> failwith ""Called Wneg"")".
(* rethink combine *)
Extract Constant combine => "(fun s w s' w' -> Int64.logor (Int64.shift_left w' s) w)".
Extract Constant wordToNat => "(fun _ w -> Int64.to_int w)". (* Not ideal *)
Extract Constant natToWord => "(fun _ w -> Int64.of_int w)".
Extract Constant wzero => "(fun _ -> Int64.zero)".
Extract Constant wzero' => "(fun _ -> Int64.zero)".
Extract Constant wones => "(fun n -> Int64.sub (Int64.shift_left Int64.one n) Int64.one)".

Extract Constant SW_word => "(fun sz b n -> Int64.add (if b then Int64.shift_left Int64.one sz else Int64.zero) n)".

Extract Inductive Word.word =>
int64 ["Int64.zero" "(fun (b, _, w') -> Int64.add (if b then Int64.one else Int64.zero) (Int64.shift_left w' 1))"]
      "failwith ""Destructing an int64""".
Extract Constant encode_word' => "encode_word'_recurse_on_size".

Extract Inlined Constant fst => "fst".
Extract Inlined Constant snd => "snd".
Extraction Inline test_cache.

Extract Inlined Constant char => "int64".
Extract Constant rev => "List.rev".
Extract Constant app => "List.append".
Extract Constant length => "List.length".

Extract Constant wordToN => "(fun _ w -> w)". (* Not ideal *)

Extract Inductive positive => int64
[ "(fun p->(Int64.add Int64.one (Int64.mul (Int64.of_int 2) p)))" "(fun p->(Int64.mul (Int64.of_int 2) p))" "Int64.one" ]
"(fun f2p1 f2p f1 p ->
   if p<=Int64.one then f1 () else if (Int64.rem p (Int64.of_int 2)) = Int64.zero then f2p (Int64.div p (Int64.of_int 2)) else f2p1 (Int64.div p (Int64.of_int 2)))".

Extract Constant Pos.add => "Int64.add".
Extract Constant Pos.succ => "Int64.succ".
Extract Constant Pos.pred => "fun n -> Pervasives.max Int64.zero (Int64.sub n Int64.one)".
Extract Constant Pos.sub => "fun n m -> Pervasives.max Int64.zero (Int64.sub n m)".
Extract Constant Pos.mul => "Int64.mul".
Extract Constant Pos.min => "Pervasives.min".
Extract Constant Pos.max => "Pervasives.max".
Extract Constant Pos.compare =>
 "fun x y -> if x=y then Eq else if x<y then Lt else Gt".
Extract Constant Pos.compare_cont =>
 "fun c x y -> if x=y then c else if x<y then Lt else Gt".



Extract Inductive N => int64 [ "Int64.zero" "" ]
"(fun f0 fp n -> if n=Int64.zero then f0 () else fp n)".

Extract Constant N.add => "Int64.add".
Extract Constant N.succ => "Int64.succ".
Extract Constant N.pred => "fun n -> Pervasives.max Int64.zero (Int64.sub n Int64.one)".
Extract Constant N.sub => "fun n m -> Pervasives.max Int64.zero (Int64.sub n m)".
Extract Constant N.mul => "Int64.mul".
Extract Constant N.min => "Pervasives.min".
Extract Constant N.max => "Pervasives.max".
Extract Constant N.div => "fun a b -> if b=Int64.zero then Int64.zero else (Int64.div a b)".
Extract Constant N.modulo => "fun a b -> if b=Int64.zero then a else Int64.rem a b".
Extract Constant N.compare =>
 "fun x y -> if x=y then Eq else if x<y then Lt else Gt".

Extract Constant N.shiftl => "fun a b -> Int64.shift_left a (Int64.to_int b)".
Extract Constant N.shiftr => "fun a b -> Int64.shift_right_logical a (Int64.to_int b)".
Extract Constant N.lor => "Int64.logor".
Extract Constant N.land => "Int64.logand".
Extract Constant N.eqb => "(=)".
Extract Constant N.eq_dec => "(=)".
Extract Constant N.ltb => "(<)".
Extract Constant N.div2 => "(fun x -> Int64.div x (Int64.of_int 2))".
(* Extract Constant N.div_eucl => "(fun x y -> (Int64.div x y, Int64.rem x y))". *)
Extract Constant Varint_split => "(fun n -> (Int64.shift_right_logical n 7, Int64.logand n 127L))".
(* :TODO: Get rid of power and instead use bit operations *)
Extract Constant N.pow => "Batteries.Int64.pow".
