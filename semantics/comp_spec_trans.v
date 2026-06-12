From stdpp Require Import prelude strings gmap stringmap functions countable sets propset.
From Spec Require Import comp_spec_defs comp_spec_meta.

Section Trans.

(* type of behaviors of source code *)
Variable b_SourceCode : Type.

(* type of behaviors of machine code *)
Variable b_MachineCode : Type.

(* type of observable behaviors *)
Variable b_Observation : Type.

(* set of possible source code behaviors *)
Variable B_SourceCode : propset b_SourceCode.

(* set of possible machine code behaviors *)
Variable B_MachineCode : propset b_MachineCode.

(* observation of source code behavior *)
Variable observe_SourceCode : b_SourceCode -> b_Observation.

(* observation of machine code of behavior *)
Variable observe_MachineCode : b_MachineCode -> b_Observation.

(* abstractly compile source component and model to machine component and model *)
Variable compile_c : c -> (cn -> propset b_SourceCode) -> (q -> propset b_SourceCode) ->
 c * (cn -> propset b_MachineCode) * (q -> propset b_MachineCode).

Definition observation_set_MachineCode
  (X : propset b_MachineCode) : propset b_Observation :=
 {[ x | exists y, y ∈ X /\ observe_MachineCode y = x ]}.

Definition observation_set_SourceCode
  (X : propset b_SourceCode) : propset b_Observation :=
 {[ x | exists y, y ∈ X /\ observe_SourceCode y = x ]}.

(* correct compilation is when observations are subset *)
Definition correct_compile_c : Prop :=
  forall (c_src c_mc : c) Mc Mq Mc' Mq',
   compile_c c_src Mc Mq = (c_mc, Mc', Mq') ->
   (observation_set_MachineCode (c_sem Mc' Mq' c_mc)) ⊆
   (observation_set_SourceCode (c_sem Mc Mq c_src)).

(* 
 correct compilation means we don't have to verify machine code
 to know a specification holds for compilation output 
*)
Lemma correct_compile_c_obviates_machine_code_verification :
  correct_compile_c ->
  forall c_src c_mc Mc Mc' Mq Mq',
    compile_c c_src Mc Mq = (c_mc, Mc', Mq') -> (* compile source *)
    forall S_src MS MV,
     P_sem B_SourceCode Mc MS Mq MV (P_implements c_src S_src) -> (* prove source specification *)
     exists X, X ∈ S_sem B_SourceCode MS MV S_src /\
      observation_set_MachineCode (c_sem Mc' Mq' c_mc) ⊆ observation_set_SourceCode X.
Proof.
unfold correct_compile_c.
simpl.
intros.
set_solver.
Qed.

(* abstractly translate source specification and model to machine specification and model *)
Variable translate_S : S -> (Sn -> propset (propset b_SourceCode)) ->
 (V -> propset (propset b_SourceCode)) ->
 S * (Sn -> propset (propset b_MachineCode)) * (V -> propset (propset b_MachineCode)).

(* correct specification translation is when machine code observations are subset of source code observations *)
Definition correct_translate_S : Prop :=
 forall (S_src S_mc : S) MS MV MS' MV',
 translate_S S_src MS MV = (S_mc, MS', MV') ->
 forall X, X ∈ S_sem B_MachineCode MS' MV' S_mc ->
  exists Y, Y ∈ S_sem B_SourceCode MS MV S_src /\
   observation_set_MachineCode X ⊆ observation_set_SourceCode Y.

(* 
 correct translation means that, regardless of the compiler,
 it suffices to verify machine code for translated specification
 to be ensured that the source specification holds for machine code.
*)
Lemma correct_translate_S_obviates_correct_compilation : 
 correct_translate_S ->
 forall c_src c_mc Mc Mq Mc' Mq',
   compile_c c_src Mc Mq = (c_mc, Mc', Mq') -> (* compile program arbitrarily *)
   forall (S_src S_mc : S) MS MV MS' MV',
    translate_S S_src MS MV = (S_mc, MS', MV') -> (* translate specification *)
    P_sem B_MachineCode Mc' MS' Mq' MV' (P_implements c_mc S_mc) -> (* prove specification *)
     exists X, X ∈ S_sem B_SourceCode MS MV S_src /\
      observation_set_MachineCode (c_sem Mc' Mq' c_mc) ⊆ observation_set_SourceCode X.
Proof.
unfold correct_translate_S.
simpl.
intros.
set_solver.
Qed.

End Trans.
