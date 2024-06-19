/// BA.Preds
/// ==============

module BA.Preds

open SecrecyLabels
open GlobalRuntimeLib
open CryptoLib
module A = LabeledCryptoAPI
module LAPI = LabeledRuntimeAPI
module LPKI = LabeledPKI
open Communication.Layer


open BA.Messages
open BA.Sessions

(*! Global Usage *)

(* don't allow any crypto functions *)
let pke_pred (i:timestamp) (s:string) (pk:bytes) (m:bytes) :prop = False
let aead_pred i s k m ad :prop  = False
let sign_pred i s k m :prop = False
let mac_pred i s k m :prop = False


let ba_usage_preds : A.usage_preds = {
  A.can_pke_encrypt = pke_pred;
  A.can_aead_encrypt = aead_pred;
  A.can_sign = sign_pred;
  A.can_mac = mac_pred
}


let ba_gu: A.global_usage = {
  A.usage_preds = ba_usage_preds;
  A.key_usages = A.default_key_usages
}


(*! Send Predicates *)


(**
  Do not allow single send functions, as we don't use them in this example.
*)
let confidential_send_pred trace_idx m : prop = False
let authenticated_send_pred (trace_idx:timestamp) m : prop = False
let authenticated_confidential_send_pred (trace_idx:timestamp) m : prop= False

(** Both account generation and access requests can be sent
    without any pre-conditions.
    Other messages can not be sent as a request.
*)
let request_send_pred (trace_idx:timestamp) m : prop =
  match parse_msg_raw m with
  | Success (GenerateAccountReq password)
  | Success (GetSecretReq password) -> True
  | _ -> False // do not allow responses to be sent over a confidential-only channel

(** An account registration response can be sent in any case.

    An access response can only be sent in response to an access request,
    and only if the label of the [secret] is the same as
    the label of the [password] sent in the request.
*)
let response_send_pred (trace_idx:timestamp) m request sym_key : prop =
  match parse_msg_raw m with
  | Success (GenerateAccountResp status) -> True
  | Success (GetSecretResp secret) -> (
            match parse_msg_raw request with
            | Success (GetSecretReq password) ->
                 (was_rand_generated_before trace_idx secret (A.get_label ba_gu.A.key_usages password) (nonce_usage "BA.Secret"))
            | _ -> False
  )
  | _ -> False // only responses may be sent over authn+conf channels


let ba_send_function_preds:predicates_for_send_functions = {
  confidential_send_pred = confidential_send_pred;
  authenticated_send_pred = authenticated_send_pred;
  authenticated_confidential_send_pred = authenticated_confidential_send_pred;
  request_pred = request_send_pred;
  response_pred = response_send_pred;
}


(*! Extended Global Usage *)
(* extends the global usage with the send predicates *)
let ba_extended_gu:extended_global_usage = {
  higher_layer_gu = ba_gu;
  send_function_predicates = ba_send_function_preds;
}


(*! Event Predicate *)

let epred (i:timestamp) s e : prop = False // we don't use (and thus allow) events in this example


(*! State Invariant *)

let session_st_inv (trace_idx:timestamp) (p:principal) (si:nat) (vi:nat) (st:bytes) : prop =
  match parse_server_session_state st, parse_client_session_state st with
  | Some (ServerAccountSession password secret), None -> (
     // the password and secret stored in a server session have to have the same label ...
     (A.get_label ba_gu.A.key_usages secret) == (A.get_label ba_gu.A.key_usages password) /\
     // ... and the secret has to have the correct usage
     (was_rand_generated_before trace_idx secret (A.get_label ba_gu.A.key_usages password) (nonce_usage "BA.Secret"))
  )
  | None, Some (ClientSession initiator server password opt_secret opt_latest_get_secret_request_idx) ->
    // a client [p] can only store sessions it initiated itself
    initiator = p /\
    // the password stored for the server has to have the label [client, server] ...
    (A.get_label ba_gu.A.key_usages password) == (readers [P p; P server]) /\
    // ... and the correct usage
    was_rand_generated_before trace_idx password (readers [(P p); (P server)]) (nonce_usage "BA.Password") /\

    // a client can only store a secret, if ...
    (Some? opt_secret ==>
      ( // ... the client or the server are corrupted
        (A.corrupt_id trace_idx (P initiator) \/ A.corrupt_id trace_idx (P server)) \/

        // ... or
        // the secret has label [client, server] and the correct usage
        ((A.get_label ba_gu.A.key_usages (Some?.v opt_secret)) == (readers [P p; P server]) /\
         (was_rand_generated_before trace_idx (Some?.v opt_secret) (A.get_label ba_gu.A.key_usages password) (nonce_usage "BA.Secret"))
        )
    )
    )/\

    // after sending an access request, the client stores the index of this request ensuring ...
    (Some? opt_latest_get_secret_request_idx ==>
      ( // ... that there is a request at this index and
        // that the request contains the password that is also stored in this session
      let latest_get_secret_request_idx = Some?.v opt_latest_get_secret_request_idx in
      exists request sym_key. is_request_at_idx request latest_get_secret_request_idx sym_key /\
        (
          match parse_msg_raw request with
          | Success (GetSecretReq password_in_request) -> password_in_request == password
          | _ -> False
        )
      )
    )
  | _ -> True


let session_st_inv_later (i:timestamp) (j:timestamp) (p:principal) (si:nat) (vi:nat) (st:bytes) :
                   Lemma ((session_st_inv i p si vi st /\ later_than j i) ==>
                           session_st_inv j p si vi st) = ()

(*! Complete Set of Predicates *)

(** an instance of the predicates exposed by the communication layer *)
let ba_preds:send_layer_preds = {
  extended_higher_layer_gu = ba_extended_gu;
  epred = epred;
  session_st_inv = session_st_inv;
  session_st_inv_later = session_st_inv_later;
}


(* shorter names for commonly used usages *)
let gu = ba_preds.extended_higher_layer_gu // == ba_extended_gu
let ba_key_usages = gu.higher_layer_gu.key_usages // == ba_gu.key_usages
