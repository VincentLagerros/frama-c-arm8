From stdpp Require Import prelude strings gmap stringmap functions countable sets propset.
From Spec Require Import comp_spec_defs.

Section Util.

Context {A : Type}.

Definition double_intersection
 (s1 : propset (propset A))
 (s2 : propset (propset A)) : propset (propset A) :=
{[ x | exists a b, x ≡ a ∩ b /\ a ∈ s1 /\ b ∈ s2 ]}.

Definition downward_closed (s : propset (propset A)) : Prop :=
forall e, e ∈ s -> (forall e', e' ⊆ e -> e' ∈ s).

Definition pow (s : propset A) : propset (propset A) :=
{[ x | x ⊆ s ]}.

End Util.

Section Sem.

Context {A : Type}.

Fixpoint c_sem
 (Mc : cn -> propset A)
 (Mq : q -> propset A)
 (c0 : c) : propset A :=
match c0 with
| c_const cn1 =>
    Mc cn1
| c_comp c1 c2 =>
    c_sem Mc Mq c1 ∩ c_sem Mc Mq c2
| c_var q1 =>
    Mq q1
end.

Fixpoint S_sem (omega : propset A)
 (MS : Sn -> propset (propset A))
 (MV : V -> propset (propset A))
 (S0 : S) : propset (propset A) :=
match S0 with
| S_const (Sc_const Sn0) =>
    MS Sn0
| S_conj S1 S2 =>
    S_sem omega MS MV S1 ∩ S_sem omega MS MV S2
| S_assume S1 S2 => 
    {[ B | B ∈ pow omega /\
       (forall B', B' ∈ S_sem omega MS MV S1 -> B ∩ B' ∈ S_sem omega MS MV S2) ]}
| S_par S1 S2 =>
    double_intersection (S_sem omega MS MV S1) (S_sem omega MS MV S2)
| S_var V1 =>
    MV V1
| S_const Sc_compat =>
    {[ B | B ∈ pow omega /\ B ≢ ∅ ]}
| S_const Sc_top =>
    {[ omega ]}
end.

Fixpoint P_sem (omega : propset A)
 (Mc : cn -> propset A) 
 (MS : Sn -> propset (propset A))
 (Mq : q -> propset A)
 (MV : V -> propset (propset A))
 (P0 : P) : Prop :=
match P0 with
| P_implements c1 S1 =>
    c_sem Mc Mq c1 ∈ S_sem omega MS MV S1
| P_refines S1 S2 =>
    S_sem omega MS MV S1 ⊆ S_sem omega MS MV S2
| P_asserts S1 =>
    downward_closed (S_sem omega MS MV S1)
| P_forall_c q1 P1 =>
    forall qs, qs ⊆ omega -> P_sem omega Mc MS (<[ q1 := qs ]>Mq) MV P1
| P_exists_c q1 P1 =>
    exists qs, qs ⊆ omega /\ P_sem omega Mc MS (<[ q1 := qs ]>Mq) MV P1
| P_forall_S V1 P1 =>
    forall Vs, Vs ⊆ pow omega -> P_sem omega Mc MS Mq (<[ V1 := Vs ]>MV) P1
| P_exists_S V1 P1 =>
    exists Vs, Vs ⊆ pow omega /\ P_sem omega Mc MS Mq (<[ V1 := Vs ]>MV) P1
| P_implies P1 P2 =>
    P_sem omega Mc MS Mq MV P1 -> P_sem omega Mc MS Mq MV P2
| P_and P1 P2 =>
    P_sem omega Mc MS Mq MV P1 /\ P_sem omega Mc MS Mq MV P2
| P_or P1 P2 =>
    P_sem omega Mc MS Mq MV P1 \/ P_sem omega Mc MS Mq MV P2
| P_not P1 =>
    ~ P_sem omega Mc MS Mq MV P1
| P_c_eq c1 c2 =>
    c_sem Mc Mq c1 = c_sem Mc Mq c2
| P_S_eq S1 S2 =>
    S_sem omega MS MV S1 = S_sem omega MS MV S2
end.

End Sem.
