/// ISODH.Messages (implementation)
/// ================================
module ISODH.Messages

module A = LabeledCryptoAPI
module Att = AttackerAPI

%splice [ps_sigval_generic] (gen_parser (`sigval_generic))
%splice [ps_sigval_generic_is_well_formed] (gen_is_well_formed_lemma (`sigval_generic))

instance sigval_parseable_serializeable: parseable_serializeable bytes sigval
 = mk_parseable_serializeable ps_sigval_generic

let parse_sigval t : result sigval =
  match (parse sigval t) with
  | Some x -> Success x
  | None -> Error "can't parse sigval"

instance sigval_pub_parseable_serializeable: (i:timestamp) -> parseable_serializeable (Att.pub_bytes i) (sigval_pub i)
 = fun i -> mk_parseable_serializeable ps_sigval_generic

let parse_sigval_pub i t : result (sigval_pub i) =
  match (parse (sigval_pub i) t) with
  | Some x -> Success x
  | None -> Error "can't parse sigval"


let sigval_msg2 (#i:nat) (b:principal) (gx:msg i public) (gy:msg i public) = //: msg i public =
  parse_serialize_inv_lemma #bytes sigval (SigMsg2 b gx gy);
  serialize_wf_lemma sigval (ComparseGlue.is_msg isodh_global_usage public i) (SigMsg2 b gx gy);
  (serialize sigval (SigMsg2 b gx gy) <: bytes)

let sigval_pub_msg2 (#i:nat) (b:principal) (gx:Att.pub_bytes i) (gy:Att.pub_bytes i) =
  parse_serialize_inv_lemma #(Att.pub_bytes i) (sigval_pub i) (SigMsg2 b gx gy);
  serialize_wf_lemma #(Att.pub_bytes i) (sigval_pub i) (Att.attacker_knows_at i) (SigMsg2 b gx gy);
  (serialize (sigval_pub i) (SigMsg2 b gx gy) <: Att.pub_bytes i)



let sigval_msg3 (#i:nat) (a:principal) (gx:msg i public) (gy:msg i public) = //: msg i public =
  parse_serialize_inv_lemma #bytes sigval (SigMsg3 a gx gy);
  serialize_wf_lemma sigval (ComparseGlue.is_msg isodh_global_usage public i) (SigMsg3 a gx gy);
  (serialize sigval (SigMsg3 a gx gy) <: bytes)

let sigval_pub_msg3 (#i:nat) (a:principal) (gx:Att.pub_bytes i) (gy:Att.pub_bytes i) =
  parse_serialize_inv_lemma #(Att.pub_bytes i) (sigval_pub i) (SigMsg3 a gx gy);
  serialize_wf_lemma #(Att.pub_bytes i) (sigval_pub i) (Att.attacker_knows_at i) (SigMsg3 a gx gy);
  (serialize (sigval_pub i) (SigMsg3 a gx gy) <: Att.pub_bytes i)


%splice [ps_iso_msg_generic] (gen_parser (`iso_msg_generic))
//%splice [ps_iso_msg_generic_is_well_formed] (gen_is_well_formed_lemma (`iso_msg_generic))

instance iso_msg_parseable_serializeable (i:nat) : parseable_serializeable (msg i public) (iso_msg i)
 = mk_parseable_serializeable (ps_iso_msg_generic i)

let serialize_msg (i:nat) (m:iso_msg i) : msg i public =
  serialize _ m



let parse_msg (#i:nat) (w:msg i public) : result (iso_msg i) =
  match parse _ w with
  | Some res -> Success res
  | None -> Error "parse_msg: bad format"

//This sanity check can be removed?
let parse_serialize_msg_lemma #i m : Lemma (parse_msg #i (serialize_msg i m) == Success m) =
  parse_serialize_inv_lemma #(msg i public) _ m


instance iso_msg_parseable_serializeable_pub_bytes (i:nat) : parseable_serializeable (Att.pub_bytes i) (iso_msg_pub i)
 = mk_parseable_serializeable (ps_iso_msg_generic i)

let serialize_msg_pub (i:nat) (m:iso_msg_pub i) : Att.pub_bytes i =
  serialize _ m

let parse_msg_pub (#i:nat) (w:Att.pub_bytes i) : result (iso_msg_pub i) =
  match parse _ w with
  | Some res -> Success res
  | None -> Error "parse_msg: bad format"
