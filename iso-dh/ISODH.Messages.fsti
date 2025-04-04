/// ISODH.Messages
/// ===============
module ISODH.Messages

open Comparse
open ComparseGlue

open SecrecyLabels
open GlobalRuntimeLib
open CryptoLib
 
module A = LabeledCryptoAPI
module Att = AttackerAPI

(* Events *)

let initiate (a:principal) (b:principal) (gx:bytes) : event = ("Initiate",[(string_to_bytes a);(string_to_bytes b);gx])
let respond (a:principal) (b:principal) (gx:bytes) (gy:bytes) (y:bytes): event = ("Respond",[(string_to_bytes a);(string_to_bytes b);gx;gy;y])
let finishI (a:principal) (b:principal) (gx:bytes) (gy:bytes) (k:bytes): event = ("FinishI",[(string_to_bytes a);(string_to_bytes b);gx;gy;k])
let finishR (a:principal) (b:principal) (gx:bytes) (gy:bytes) (k:bytes): event = ("FinishR",[(string_to_bytes a);(string_to_bytes b);gx;gy;k])

(* Formats of Signed Values *)
noeq type sigval_generic (bytes:Type0) {|bytes_like bytes|}  =
  | SigMsg2: a:principal -> gx:bytes -> gy:bytes -> sigval_generic bytes
  | SigMsg3: b:principal -> gx:bytes -> gy:bytes -> sigval_generic bytes

type sigval = sigval_generic bytes

val parse_sigval: bytes -> result sigval

type sigval_pub (i:timestamp) = sigval_generic (Att.pub_bytes i)
val parse_sigval_pub: (i:timestamp) -> Att.pub_bytes i -> result (sigval_pub i)

let sig_key_label = "ISODH.sig_key"
let aead_key_label = "ISODH.aead_key"
let dh_key_label = "ISODH.dh_key"

(* Global Key Usages *)
let dh_shared_secret_usage s1 s2 ss =
  if s1 = "ISODH.dh_key" then Some (aead_usage aead_key_label)
  else if s2 = "ISODH.dh_key" then Some (aead_usage aead_key_label)
  else None
let dh_unknown_peer_usage s1 ss = if s1 = dh_key_label then Some (aead_usage aead_key_label) else None

let isodh_key_usages : A.key_usages = {
  A.dh_shared_secret_usage = dh_shared_secret_usage;
  A.dh_unknown_peer_usage = dh_unknown_peer_usage;
  A.dh_usage_commutes_lemma = (fun () -> ());
  A.dh_unknown_peer_usage_lemma = (fun () -> ());
  A.kdf_extend_label = (fun s k slt kl sl -> Some private_label);
  A.kdf_extract_usage = (fun s k slt -> None);
  A.kdf_expand_usage = (fun s k info -> None);
}

let ppred i s pk m: prop = True
let apred i s k m ad: prop = True
let spred i s k m: prop =
    if s = sig_key_label then
    (exists p. A.get_signkey_label isodh_key_usages k == readers [P p] /\
	(match parse_sigval m with
	 | Success (SigMsg2 a gx gy) ->
	   (exists y. gy == (dh_pk y) /\ did_event_occur_before i p (respond a p gx gy y))
	 | Success (SigMsg3 b gx gy) ->
	   (exists x. gx == (dh_pk x) /\ did_event_occur_before i p (finishI p b gx gy (dh x gy)))
	 | _ -> False))
    else False
let mpred i s k m: prop = True

let isodh_usage_preds : A.usage_preds = {
  A.can_pke_encrypt = ppred;
  A.can_aead_encrypt =  apred;
  A.can_sign = spred;
  A.can_mac = mpred
}

let isodh_global_usage : A.global_usage = {
  A.key_usages = isodh_key_usages;
  A.usage_preds = isodh_usage_preds;
}

(* Messages and Serialization *)

let msg i l = A.msg isodh_global_usage i l

val sigval_msg2 (#i:nat) (b:principal) (gx:msg i public) (gy:msg i public) :
		r:msg i public{parse_sigval r == Success (SigMsg2 b gx gy)}

val sigval_pub_msg2 (#i:nat) (b:principal) (gx:Att.pub_bytes i) (gy:Att.pub_bytes i) :
		r:Att.pub_bytes i{parse_sigval_pub i r == Success (SigMsg2 b gx gy)}


val sigval_msg3 (#i:nat) (a:principal) (gx:msg i public) (gy:msg i public) :
		r:msg i public{parse_sigval r == Success (SigMsg3 a gx gy)}

val sigval_pub_msg3 (#i:nat) (a:principal) (gx:Att.pub_bytes i) (gy:Att.pub_bytes i) :
		r:Att.pub_bytes i{parse_sigval_pub i r == Success (SigMsg3 a gx gy)}


noeq type iso_msg_generic (bytes:Type0) {|bytes_like bytes|} (i:nat) =
  |Msg1: a:principal -> gx:bytes -> iso_msg_generic bytes i
  |Msg2: b:principal -> gy:bytes -> sg:bytes -> iso_msg_generic bytes i
  |Msg3: sg:bytes -> iso_msg_generic bytes i

type iso_msg (i:nat) = iso_msg_generic (msg i public) i

val serialize_msg: i:nat -> iso_msg i -> msg i public
val parse_msg: #i:nat -> msg i public -> result (iso_msg i)

let iso_msg_pub (i:nat) = iso_msg_generic (Att.pub_bytes i) i
val serialize_msg_pub: i:nat -> iso_msg_pub i -> Att.pub_bytes i
val parse_msg_pub: #i:nat -> Att.pub_bytes i -> result (iso_msg_pub i)


