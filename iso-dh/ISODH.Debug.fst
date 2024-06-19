/// ISO_DH.Debug (implementation)
/// ==============================
module ISODH.Debug

open SecrecyLabels
open CryptoLib
open GlobalRuntimeLib
open LabeledCryptoAPI
open LabeledRuntimeAPI
open LabeledPKI
open AttackerAPI
open ISODH.Messages
open ISODH.Sessions
open ISODH.Protocol
open SecurityLemmas

val benign_attacker:
  unit ->
  LCrypto unit (pki isodh)
  (requires fun _ -> True)
  (ensures fun _ _ _ -> True)

let benign_attacker () =
  let alice:principal = "alice" in
  let bob:principal = "bob" in
  let t0 = global_timestamp () in
  let pka = gen_private_key #isodh #t0 alice SIG "ISODH.sig_key" in
  let t1 = global_timestamp () in
  let pkb = gen_private_key #isodh #t1 bob SIG "ISODH.sig_key" in
  let t2 = global_timestamp () in
  assert (later_than t1 t0);
  assert (later_than t2 t1);
  let idx_pka_b = install_public_key #isodh #t2 bob alice SIG "ISODH.sig_key" in
  let t3 = global_timestamp () in
  let idx_pkb_a = install_public_key #isodh #t3 alice bob SIG "ISODH.sig_key" in
  let (idx_msg_1, idx_sess_a) = initiator_send_msg_1 alice bob in
  let (idx_msg_2, idx_sess_b) = responder_send_msg_2 bob idx_msg_1 in
  let idx_msg_3 = initiator_send_msg_3 alice idx_sess_a idx_msg_2 in
  responder_accept_msg_3 bob idx_sess_b idx_msg_3

let benign () : LCrypto unit (pki isodh)
  (requires (fun _ -> True)) (ensures (fun _ _ _ -> True)) =
  print_string "start\n";
  let t0 = get() in
  let x = benign_attacker () in
  print_trace ()

val query_secret_key:
    idx_state:nat -> idx_corrupt:nat -> idx_query:nat ->
    p:principal -> LCrypto (pub_bytes idx_query) (pki isodh)
    (requires (fun t0 -> idx_state < idx_query /\ idx_corrupt < idx_query /\ idx_query <= trace_len t0 /\ was_corrupted_at idx_corrupt p 0 0))
    (ensures (fun t0 _ t1 -> trace_len t1 == trace_len t0))
let query_secret_key idx_state idx_corrupt idx_query p =
    let t = query_state_i idx_state idx_corrupt idx_query p 0 0 in
    match split t with 
    | Success (tag, b) -> 
      (match split b with 
      | Success (tag, b) -> b 
      | _ -> b)
    | _ -> error "incorrect tag"

val key_synch_attacker:
  unit ->
  LCrypto unit (pki isodh)
  (requires fun _ -> True)
  (ensures fun _ _ _ -> True)

#push-options "--z3rlimit 300 --max_fuel 0 --max_ifuel 0"
let key_synch_attacker () =
  let alice:principal = "alice" in
  let bob:principal = "bob" in
  let mallory:principal = "mallory" in
  let t0 = global_timestamp () in
  let pka = gen_private_key #isodh #t0 alice SIG "ISODH.sig_key" in
  let t1 = global_timestamp () in
  let pkb = gen_private_key #isodh  #t1 bob SIG "ISODH.sig_key" in
  let t2 = global_timestamp () in
  let pkm = gen_private_key #isodh #t2 mallory SIG "ISODH.sig_key" in
  let t3 = global_timestamp () in
  let t4 = compromise mallory 0 0 in
  let t5 = global_timestamp () in
  let skm = query_secret_key (t2+1) t3 t5 mallory in
  let idx_pkm_b = install_public_key #isodh #t5 mallory bob SIG "ISODH.sig_key" in
  let t6 = global_timestamp () in
  let idx_pkm_a = install_public_key #isodh #t6 mallory alice SIG "ISODH.sig_key" in
  let (idx_msg1, idx_sess_a) = initiator_send_msg_1 alice mallory in
  let t7 = global_timestamp () in
  let (|t8,w_msg1|) = receive_i idx_msg1 mallory in
  attacker_only_knows_publishable_values (pki isodh) w_msg1;
  match parse_msg_pub #t8 w_msg1 with
  | Success (Msg1 alice gx) -> begin
      let msg1' = Msg1 mallory gx in
      let w_msg1' = serialize_msg_pub t8 msg1' in
      let idx_msg1' = send #t8 mallory bob w_msg1' in
      let (idx_msg2, idx_sess_b) = responder_send_msg_2 bob idx_msg1' in
      let t9 = global_timestamp () in
      let (|_,w_msg2|) = receive_i idx_msg2 mallory in
      match parse_msg_pub #t9 w_msg2 with
      | Success (Msg2 b gy sg) -> begin
          attacker_only_knows_publishable_values (pki isodh) gx;
          attacker_only_knows_publishable_values (pki isodh) gy;
          let sv' = sigval_pub_msg2 #t9 alice gx gy in
          let (| t10, n_sig |) = pub_rand_gen (nonce_usage "SIG_NONCE") in
	  let sg' = sign #t10 skm n_sig sv' in
          let msg2' = Msg2 mallory gy sg' <: iso_msg_pub t10 in
          let w_msg2' = serialize_msg_pub t10 msg2' in
          let idx_msg2' = send mallory alice w_msg2' in
	  let idx_msg3 = initiator_send_msg_3 alice idx_sess_a idx_msg2' in
	  let (|_,w_msg3|) = receive_i idx_msg3 mallory in
          match parse_msg_pub w_msg3 with
          | Success (Msg3 _ ) -> begin
              let sv' = sigval_pub_msg3 #t10 b gx gy in
              let (| t10, n_sig |) = pub_rand_gen (nonce_usage "SIG_NONCE") in
	      let sg':pub_bytes t10  = sign #t10 skm n_sig sv' in
              let msg3' = Msg3 sg' in
              let w_msg3' = serialize_msg_pub t10 msg3' in
              let idx_msg3' = send mallory bob w_msg3' in
	      responder_accept_msg_3 bob idx_sess_b idx_msg3'
            end
          | _ -> error "not a msg3 form alice"
        end
      | _ -> error "not a msg2 from bob"
    end
  | _ -> error "not a msg1 from alice"
#pop-options


let key_synch () : LCrypto unit (pki isodh) (requires (fun _ -> True)) (ensures (fun _ _ _ -> True)) =
  print_string "key synch start\n";
  let x = key_synch_attacker () in
  print_trace ()


let main =
  IO.print_string "======================\n";
  IO.print_string "       ISO-DH        \n";
  IO.print_string "======================\n";
  let t0 = Seq.empty in
  IO.print_string "Starting Benign Attacker:\n";
  assume(valid_trace (pki isodh) t0);
  let r,t1 = (reify (benign ()) t0) in
  (match r with
  | Error s -> IO.print_string ("ERROR: "^s^"\n")
  | Success _ -> IO.print_string "PROTOCOL RUN (SUCCESS for jenkins): Successful execution of ISO-DH protocol.\n");
  IO.print_string "Finished Benign Attacker:\n";
  IO.print_string "Starting Key-Synch Attacker:\n";
  assume(valid_trace (pki isodh) t0);
  let r,t1 = (reify (key_synch ()) t0) in
  (match r with
  | Error s -> IO.print_string ("ERROR: "^s^"\n")
  | Success _ -> IO.print_string "PROTOCOL RUN (SUCCESS for jenkins): Successful key synch attack on ISO-DH protocol.\n");
  IO.print_string "Finished Key-Synch Attacker:\n"



