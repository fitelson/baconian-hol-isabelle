theory Bacon_Abbreviations
  imports Bacon_Base.Bacon_Deduction
begin

section \<open>Bacon-style logical abbreviations and axiom schemata\<close>

definition prop_bin_ty :: otype where
  "prop_bin_ty = Prop \<rightarrow>\<^sub>o Prop \<rightarrow>\<^sub>o Prop"

definition pred_ty :: "otype \<Rightarrow> otype" where
  "pred_ty \<sigma> = \<sigma> \<rightarrow>\<^sub>o Prop"

definition identity_ty :: "otype \<Rightarrow> otype" where
  "identity_ty \<sigma> = \<sigma> \<rightarrow>\<^sub>o \<sigma> \<rightarrow>\<^sub>o Prop"

definition quantifier_ty :: "otype \<Rightarrow> otype" where
  "quantifier_ty \<sigma> = pred_ty \<sigma> \<rightarrow>\<^sub>o Prop"

definition ObjDisj :: "oterm \<Rightarrow> oterm \<Rightarrow> oterm" (infixr "\<or>\<^sub>o" 30) where
  "(A \<or>\<^sub>o B) = Disj A B"

definition ObjLeq :: "oterm \<Rightarrow> oterm \<Rightarrow> oterm" (infixr "\<le>\<^sub>o" 35) where
  "(A \<le>\<^sub>o B) = Imp A B"

definition bool_comm_conj :: oterm where
  "bool_comm_conj =
    Eq prop_bin_ty
      (Lam Prop (Lam Prop (Conj (Var 1) (Var 0))))
      (Lam Prop (Lam Prop (Conj (Var 0) (Var 1))))"

definition bool_comm_disj :: oterm where
  "bool_comm_disj =
    Eq prop_bin_ty
      (Lam Prop (Lam Prop (Disj (Var 1) (Var 0))))
      (Lam Prop (Lam Prop (Disj (Var 0) (Var 1))))"

definition bool_dist_conj_disj :: oterm where
  "bool_dist_conj_disj =
    Eq (Prop \<rightarrow>\<^sub>o Prop \<rightarrow>\<^sub>o Prop \<rightarrow>\<^sub>o Prop)
      (Lam Prop (Lam Prop (Lam Prop
        (Conj (Var 2) (Disj (Var 1) (Var 0))))))
      (Lam Prop (Lam Prop (Lam Prop
        (Disj (Conj (Var 2) (Var 1)) (Conj (Var 2) (Var 0))))))"

definition bool_dist_disj_conj :: oterm where
  "bool_dist_disj_conj =
    Eq (Prop \<rightarrow>\<^sub>o Prop \<rightarrow>\<^sub>o Prop \<rightarrow>\<^sub>o Prop)
      (Lam Prop (Lam Prop (Lam Prop
        (Disj (Var 2) (Conj (Var 1) (Var 0))))))
      (Lam Prop (Lam Prop (Lam Prop
        (Conj (Disj (Var 2) (Var 1)) (Disj (Var 2) (Var 0))))))"

definition bool_dissolve_conj_disj :: oterm where
  "bool_dissolve_conj_disj =
    Eq prop_bin_ty
      (Lam Prop (Lam Prop
        (Conj (Var 1) (Disj (Var 0) (Neg (Var 0))))))
      (Lam Prop (Lam Prop (Var 1)))"

definition bool_dissolve_disj_conj :: oterm where
  "bool_dissolve_disj_conj =
    Eq prop_bin_ty
      (Lam Prop (Lam Prop
        (Disj (Var 1) (Conj (Var 0) (Neg (Var 0))))))
      (Lam Prop (Lam Prop (Var 1)))"

definition all_boolean_identities :: "oterm list" where
  "all_boolean_identities =
    [ bool_comm_conj,
      bool_comm_disj,
      bool_dist_conj_disj,
      bool_dist_disj_conj,
      bool_dissolve_conj_disj,
      bool_dissolve_disj_conj ]"

definition classic_identity_identity :: "otype \<Rightarrow> oterm" where
  "classic_identity_identity \<sigma> =
    Eq (identity_ty \<sigma>)
      (Lam \<sigma> (Lam \<sigma> (Eq \<sigma> (Var 1) (Var 0))))
      (Lam \<sigma> (Lam \<sigma>
        (Forall (pred_ty \<sigma>)
          ((App (Var 0) (Var 2)) \<longleftrightarrow>\<^sub>o (App (Var 0) (Var 1))))))"

definition classic_absorb_disj_forall :: "otype \<Rightarrow> oterm" where
  "classic_absorb_disj_forall \<sigma> =
    Eq (pred_ty \<sigma> \<rightarrow>\<^sub>o \<sigma> \<rightarrow>\<^sub>o Prop)
      (Lam (pred_ty \<sigma>) (Lam \<sigma>
        (Disj (App (Var 1) (Var 0))
          (Forall \<sigma> (App (Var 2) (Var 0))))))
      (Lam (pred_ty \<sigma>) (Lam \<sigma> (App (Var 1) (Var 0))))"

definition classic_dist_disj_forall :: "otype \<Rightarrow> oterm" where
  "classic_dist_disj_forall \<sigma> =
    Eq (pred_ty \<sigma> \<rightarrow>\<^sub>o Prop \<rightarrow>\<^sub>o Prop)
      (Lam (pred_ty \<sigma>) (Lam Prop
        (Disj (Var 0) (Forall \<sigma> (App (Var 2) (Var 0))))))
      (Lam (pred_ty \<sigma>) (Lam Prop
        (Forall \<sigma> (Disj (Var 1) (App (Var 2) (Var 0))))))"

definition classic_absorb_conj_exists :: "otype \<Rightarrow> oterm" where
  "classic_absorb_conj_exists \<sigma> =
    Eq (pred_ty \<sigma> \<rightarrow>\<^sub>o \<sigma> \<rightarrow>\<^sub>o Prop)
      (Lam (pred_ty \<sigma>) (Lam \<sigma>
        (Conj (App (Var 1) (Var 0))
          (Exists \<sigma> (App (Var 2) (Var 0))))))
      (Lam (pred_ty \<sigma>) (Lam \<sigma> (App (Var 1) (Var 0))))"

definition classic_dist_conj_exists :: "otype \<Rightarrow> oterm" where
  "classic_dist_conj_exists \<sigma> =
    Eq (pred_ty \<sigma> \<rightarrow>\<^sub>o Prop \<rightarrow>\<^sub>o Prop)
      (Lam (pred_ty \<sigma>) (Lam Prop
        (Conj (Var 0) (Exists \<sigma> (App (Var 2) (Var 0))))))
      (Lam (pred_ty \<sigma>) (Lam Prop
        (Exists \<sigma> (Conj (Var 1) (App (Var 2) (Var 0))))))"

lemma typed_bool_comm_conj:
  "\<Gamma> \<turnstile> bool_comm_conj : Prop"
  by (rule infer_type_sound) (simp add: bool_comm_conj_def prop_bin_ty_def lookup_def)

lemma typed_bool_comm_disj:
  "\<Gamma> \<turnstile> bool_comm_disj : Prop"
  by (rule infer_type_sound) (simp add: bool_comm_disj_def prop_bin_ty_def lookup_def)

lemma typed_bool_dist_conj_disj:
  "\<Gamma> \<turnstile> bool_dist_conj_disj : Prop"
  by (rule infer_type_sound) (simp add: bool_dist_conj_disj_def lookup_def)

lemma typed_bool_dist_disj_conj:
  "\<Gamma> \<turnstile> bool_dist_disj_conj : Prop"
  by (rule infer_type_sound) (simp add: bool_dist_disj_conj_def lookup_def)

lemma typed_bool_dissolve_conj_disj:
  "\<Gamma> \<turnstile> bool_dissolve_conj_disj : Prop"
  by (rule infer_type_sound) (simp add: bool_dissolve_conj_disj_def prop_bin_ty_def lookup_def)

lemma typed_bool_dissolve_disj_conj:
  "\<Gamma> \<turnstile> bool_dissolve_disj_conj : Prop"
  by (rule infer_type_sound) (simp add: bool_dissolve_disj_conj_def prop_bin_ty_def lookup_def)

lemma typed_boolean_identity:
  assumes "A \<in> set all_boolean_identities"
  shows "\<Gamma> \<turnstile> A : Prop"
  using assms
  by (auto simp: all_boolean_identities_def
      intro: typed_bool_comm_conj typed_bool_comm_disj
        typed_bool_dist_conj_disj typed_bool_dist_disj_conj
        typed_bool_dissolve_conj_disj typed_bool_dissolve_disj_conj)

lemma typed_classic_identity_identity:
  "\<Gamma> \<turnstile> classic_identity_identity \<sigma> : Prop"
  by (rule infer_type_sound) (simp add: classic_identity_identity_def identity_ty_def pred_ty_def lookup_def)

lemma typed_classic_absorb_disj_forall:
  "\<Gamma> \<turnstile> classic_absorb_disj_forall \<sigma> : Prop"
  by (rule infer_type_sound) (simp add: classic_absorb_disj_forall_def pred_ty_def lookup_def)

lemma typed_classic_dist_disj_forall:
  "\<Gamma> \<turnstile> classic_dist_disj_forall \<sigma> : Prop"
  by (rule infer_type_sound) (simp add: classic_dist_disj_forall_def pred_ty_def lookup_def)

lemma typed_classic_absorb_conj_exists:
  "\<Gamma> \<turnstile> classic_absorb_conj_exists \<sigma> : Prop"
  by (rule infer_type_sound) (simp add: classic_absorb_conj_exists_def pred_ty_def lookup_def)

lemma typed_classic_dist_conj_exists:
  "\<Gamma> \<turnstile> classic_dist_conj_exists \<sigma> : Prop"
  by (rule infer_type_sound) (simp add: classic_dist_conj_exists_def pred_ty_def lookup_def)

end
