/// SecurityLemmas
/// ===============
module SecurityLemmas

open SecrecyLabels
open CryptoLib
open CryptoEffect
open GlobalRuntimeLib
open LabeledCryptoAPI
open LabeledRuntimeAPI
module Att = AttackerAPI

let contains_corrupted_version_at (idx:timestamp) (p:id) =
    exists p' s' v'. (was_corrupted_before idx p' s' v' /\ covers p (V p' s' v'))

let corrupt_pred =
    (p:(id -> Type0){forall x y. (covers x y /\ p y) ==> p x})

let corrupt_at i : corrupt_pred =
    covers_is_transitive ();
    contains_corrupted_version_at i

val publishable_readers_implies_corruption: #i:timestamp -> l:list id ->
    Lemma (can_flow i (readers l) public ==> (exists id. can_read id (readers l) /\ corrupt_at i id))

val publishable_readers_implies_corruption2: #i:timestamp -> l:list id ->
    Lemma (can_flow i (readers l) public ==> contains_corrupt_id cpred i l)

val attacker_preserves_validity: pr:preds -> t0:trace -> t1:trace ->
    Lemma ((valid_trace pr t0 /\ Att.attacker_modifies_trace t0 t1) ==> valid_trace pr t1)
    [SMTPat (Att.attacker_modifies_trace t0 t1); SMTPat (valid_trace pr t0)]

val attacker_only_knows_publishable_values: pr:preds -> b:bytes ->
    LCrypto unit pr (requires (fun tr -> True))
                    (ensures (fun tr0 _ tr1 -> tr0 == tr1 /\
                             (Att.attacker_knows_at (trace_len tr0) b ==> is_publishable pr.global_usage (trace_len tr0) b)))

val secrecy_lemma: #pr:preds -> b:bytes ->
    LCrypto unit pr (requires (fun t0 -> True))
                    (ensures (fun t0 _ t1 -> t0 == t1 /\
                             (forall ids. (is_labeled pr.global_usage (trace_len t0) b (readers ids) /\
                                     Att.attacker_knows_at (trace_len t0) b) ==>
                                     (exists id. List.Tot.mem id ids /\ corrupt_at (trace_len t0) id))))

val secrecy_generic_label_lemma: #pr:preds -> b:bytes -> l:label ->
    LCrypto unit pr (requires (fun t0 -> True))
                    (ensures (fun t0 _ t1 -> t0 == t1 /\
                             (forall ids. (can_flow (trace_len t0) (readers ids) l /\
                                      is_labeled pr.global_usage (trace_len t0) b l /\
                                      Att.attacker_knows_at (trace_len t0) b) ==>
                                      (exists id. List.Tot.mem id ids /\ corrupt_at (trace_len t0) id))))
// TODO: This lemma is still provable with contains_corrupt_id as a postcondition, but it becomes harder to get
// information out of this (e.g. for the join lemmas). We should add more lemmas on contains_corrupt_id and/or
// can_flow. In this particular case, that readers (l1 @ l2) can flow to (join (readers l1) (readers l2)).
//                                      contains_corrupt_id cpred (trace_len t0) ids)))

val secrecy_join_label_lemma: #pr:preds -> b:bytes -> LCrypto unit pr (requires (fun t0 -> True))
                              (ensures (fun t0 _ t1 -> t0 == t1 /\
                                       (forall l l'. is_labeled pr.global_usage (trace_len t0) b (join (readers [l]) (readers [l'])) /\
                                                Att.attacker_knows_at (trace_len t0) b ==>
                                                (corrupt_at (trace_len t0) l \/ corrupt_at (trace_len t0) l'))))

val secrecy_join_label_lemma2: #pr:preds -> b:bytes -> LCrypto unit pr (requires (fun t0 -> True))
                              (ensures (fun t0 _ t1 -> t0 == t1 /\
                                       (forall l1 l2. is_labeled pr.global_usage (trace_len t0) b (join (readers l1) (readers l2)) /\
                                                Att.attacker_knows_at (trace_len t0) b ==>
//                                                contains_corrupt_id cpred (trace_len t0) (l1 @ l2))))
                                                (exists id. (List.Tot.mem id l1 \/ List.Tot.mem id l2) /\ corrupt_at (trace_len t0) id))))

val secrecy_joinall3_label_lemma: #pr:preds -> b:bytes ->
  LCrypto unit pr (requires (fun t0 -> True))
                  (ensures (fun t0 _ t1 -> t0 == t1 /\
                             (forall l1 l2 l3. is_labeled pr.global_usage (trace_len t0) b (joinAll [l1; l2; l3]) /\
                                    Att.attacker_knows_at (trace_len t0) b ==>
                                    (can_flow (trace_len t0) l1 public \/
                                     can_flow (trace_len t0) l2 public \/
                                     can_flow (trace_len t0) l3 public))))
