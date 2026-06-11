From stdpp Require Import prelude strings gmap stringmap functions countable.
From stdpp Require Import propset.
From SmallSpec Require Import small.

Section Sem.

Variable A : Type.

Variable comp : A -> A -> A.

Variable nil : A.

Variable B : propset A.

Hypothesis nil_B : nil ∈ B.

Hypothesis comp_closed : forall b1 b2,
 b1 ∈ B -> b2 ∈ B -> comp b1 b2 ∈ B.

Hypothesis comp_assoc : forall b1 b2 b3,
 comp b1 (comp b2 b3) = comp (comp b1 b2) b3.

Hypothesis comp_comm : forall b1 b2,
 comp b1 b2 = comp b2 b1.

Fixpoint c_sem
 (Mc : cn -> A)
 (c0 : c) : A :=
match c0 with
| c_const cn1 =>
    Mc cn1
| c_comp c1 c2 =>
    comp (c_sem Mc c1) (c_sem Mc c2)
end.

Fixpoint S_sem
 (MS : Sn -> propset A)
 (S0 : S) : propset A :=
match S0 with
| S_const Sn0 =>
    MS Sn0
| S_conj S1 S2 =>
    S_sem MS S1 ∩ S_sem MS S2
| S_assume S1 S2 => 
  {[ b | b ∈ B /\
     (forall b', b' ∈ S_sem MS S1 -> comp b b' ∈ S_sem MS S2) ]}
| S_par S1 S2 =>
  {[ b | b ∈ B /\ exists b1 b2, b = comp b1 b2 /\ b1 ∈ S_sem MS S1 /\ b2 ∈ S_sem MS S2 ]}
end.

Fixpoint P_sem
 (Mc : cn -> A) 
 (MS : Sn -> propset A)
 (P0 : P) : Prop :=
match P0 with
| P_implements c1 S1 =>
    c_sem Mc c1 ∈ S_sem MS S1
| P_refines S1 S2 =>
    S_sem MS S1 ⊆ S_sem MS S2
| P_implies P1 P2 =>
    P_sem Mc MS P1 -> P_sem Mc MS P2
| P_and P1 P2 =>
    P_sem Mc MS P1 /\ P_sem Mc MS P2
| P_or P1 P2 =>
    P_sem Mc MS P1 \/ P_sem Mc MS P2
| P_not P1 =>
    ~ P_sem Mc MS P1
end.

End Sem.

Section Meta.

(* type of behaviors of source code *)
Variable b_SourceCode : Type.

(* type of behaviors of machine code *)
Variable b_MachineCode : Type.

(* type of observable behaviors *)
Variable b_Observation : Type.

(* composition of source code behaviors *)
Variable b_SourceCode_comp : b_SourceCode -> b_SourceCode -> b_SourceCode.

(* composition of machine code behaviors *)
Variable b_MachineCode_comp : b_MachineCode -> b_MachineCode -> b_MachineCode.

(* set of possible source code behaviors *)
Variable B_SourceCode : propset b_SourceCode.

(* set of possible machine code behaviors *)
Variable B_MachineCode : propset b_MachineCode.

(* observation of source code *)
Variable observe_SourceCode : b_SourceCode -> b_Observation.

(* observation of machine code *)
Variable observe_MachineCode : b_MachineCode -> b_Observation.

(* abstractly compile source component and model to machine component and model *)
Variable compile_c : c -> (cn -> b_SourceCode) -> c * (cn -> b_MachineCode).

(* correct compilation is when observations are the same *)
Definition correct_compile_c : Prop :=
  forall (c_src c_mc : c) Mc Mc',
   compile_c c_src Mc = (c_mc, Mc') ->
   observe_SourceCode (c_sem b_SourceCode b_SourceCode_comp Mc c_src) =
   observe_MachineCode (c_sem b_MachineCode b_MachineCode_comp Mc' c_mc).

(* 
 correct compilation means we don't have to verify machine code
 to know a specification holds for compilation output 
*)
Lemma correct_compile_c_obviates_machine_code_verification :
  correct_compile_c ->
  forall c_src c_mc Mc Mc',
    compile_c c_src Mc = (c_mc, Mc') ->
    forall S_src MS, P_sem b_SourceCode b_SourceCode_comp B_SourceCode Mc MS (P_implements c_src S_src) ->
    observe_MachineCode (c_sem b_MachineCode b_MachineCode_comp Mc' c_mc) ∈
    {[ x | exists y, y ∈ S_sem b_SourceCode b_SourceCode_comp B_SourceCode MS S_src /\ observe_SourceCode y = x ]}.
Proof.
unfold correct_compile_c.
simpl.
intros.
set_solver.
Qed.

(* abstractly translate source specification and model to machine specification and model *)
Variable translate_S : S -> (Sn -> propset b_SourceCode) -> S * (Sn -> propset b_MachineCode).

(* correct translation is when observations are subset of source observations *)
Definition correct_translate_S : Prop :=
 forall (S_src S_mc : S) MS MS',
 translate_S S_src MS = (S_mc, MS') ->
 {[ x | exists y, y ∈ S_sem b_MachineCode b_MachineCode_comp B_MachineCode MS' S_mc /\ observe_MachineCode y = x ]} ⊆
 {[ x | exists y, y ∈ S_sem b_SourceCode b_SourceCode_comp B_SourceCode MS S_src /\ observe_SourceCode y = x ]}.

(* 
 correct translation means that, regardless of the compiler,
 it suffices to verify machine code for translated specification
 to be ensured that the source specification holds for machine code.
*)
Lemma correct_translate_S_obviates_correct_compilation : 
 correct_translate_S ->
 forall c_src c_mc Mc Mc',
   compile_c c_src Mc = (c_mc, Mc') ->
   forall (S_src S_mc : S) MS MS',
     translate_S S_src MS = (S_mc, MS') ->
     P_sem b_SourceCode b_SourceCode_comp B_SourceCode Mc MS (P_implements c_src S_src) ->
     P_sem b_MachineCode b_MachineCode_comp B_MachineCode Mc' MS' (P_implements c_mc S_mc) ->
     observe_MachineCode (c_sem b_MachineCode b_MachineCode_comp Mc' c_mc) ∈
     {[ x | exists y, y ∈ S_sem b_SourceCode b_SourceCode_comp B_SourceCode MS S_src /\ observe_SourceCode y = x ]}.
Proof.
unfold correct_translate_S.
simpl.
intros.
set_solver.
Qed.

End Meta.
