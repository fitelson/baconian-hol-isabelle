theory Bacon_Caie
  imports Bacon_S4
begin

section \<open>Caie's names layer over the Bacon object logic\<close>

text \<open>
  Caie's paper assumes the Bacon/Bacon-Dorr higher-order background logic and
  then studies names as property classifiers.  This theory starts that
  application layer inside the existing deep embedding, rather than using a
  separate shallow HOL semantics.

  Object type correspondence:
    \<^item> Caie's \<open>e\<close> is @{term Ind}.
    \<^item> Caie's \<open>t\<close> is @{term Prop}.
    \<^item> A first-order property has type \<open>e \<rightarrow> t\<close>, represented by
      @{term "pred_ty Ind"}.
    \<^item> A property classifier, the type of name meanings, has type
      \<open>(e \<rightarrow> t) \<rightarrow> t\<close>.

  Caie's counterfactual connective is added here as an uninterpreted
  object-language constant.  The Stalnaker-style counterfactual principles that
  Caie assumes should be added later as a separate axiom/rule package, so the
  definitional layer below remains conservative.
\<close>

subsection \<open>Types and primitive counterfactual connective\<close>

definition caie_prop_ty :: otype where
  "caie_prop_ty = pred_ty Ind"

definition caie_classifier_ty :: otype where
  "caie_classifier_ty = caie_prop_ty \<rightarrow>\<^sub>o Prop"

definition caie_prop_class_ty :: otype where
  "caie_prop_class_ty = caie_prop_ty \<rightarrow>\<^sub>o Prop"

definition caie_classifier_class_ty :: otype where
  "caie_classifier_class_ty = caie_classifier_ty \<rightarrow>\<^sub>o Prop"

definition caie_cf_const :: oterm where
  "caie_cf_const = Const ''caie_cf'' prop_bin_ty"

definition ObjCF :: "oterm \<Rightarrow> oterm \<Rightarrow> oterm" where
  "ObjCF A B = App (App caie_cf_const A) B"

notation ObjCF (infixr "\<box>\<rightarrow>\<^sub>o" 24)

subsection \<open>Basic property-forming operations\<close>

definition caie_heq :: "oterm \<Rightarrow> oterm" where
  "caie_heq x = Lam Ind (Eq Ind (Var 0) (shift x))"

definition caie_prop_neg :: "oterm \<Rightarrow> oterm" where
  "caie_prop_neg P = Lam Ind (Neg (App (shift P) (Var 0)))"

definition caie_top_prop :: oterm where
  "caie_top_prop = Lam Ind ObjTrue"

definition caie_bottom_prop :: oterm where
  "caie_bottom_prop = Lam Ind ObjFalse"

definition caie_exists_prop :: oterm where
  "caie_exists_prop = Lam Ind (Exists Ind (Eq Ind (Var 1) (Var 0)))"

definition caie_prop_entails :: "oterm \<Rightarrow> oterm \<Rightarrow> oterm" where
  "caie_prop_entails P R =
    \<box>\<^sub>o (Forall Ind (Imp (App (shift P) (Var 0)) (App (shift R) (Var 0))))"

notation caie_prop_entails (infixr "\<le>\<^sub>p" 35)

subsection \<open>Maximal consistency vocabulary\<close>

definition caie_GLB_op :: oterm where
  "caie_GLB_op =
    Lam caie_prop_class_ty (Lam caie_prop_ty
      (Conj
        (Forall caie_prop_ty
          (Imp (App (Var 2) (Var 0)) (Var 1 \<le>\<^sub>p Var 0)))
        (Forall caie_prop_ty
          (Imp
            (Forall caie_prop_ty
              (Imp (App (Var 3) (Var 0)) (Var 1 \<le>\<^sub>p Var 0)))
            (Var 0 \<le>\<^sub>p Var 1)))))"

definition caie_NS_op :: oterm where
  "caie_NS_op =
    Lam caie_classifier_ty
      (Forall caie_prop_ty
        ((Neg (App (Var 1) (Var 0))) \<longleftrightarrow>\<^sub>o App (Var 1) (caie_prop_neg (Var 0))))"

definition caie_UC_op :: oterm where
  "caie_UC_op =
    Lam caie_classifier_ty
      (Forall caie_prop_ty
        (Forall caie_prop_ty
          (Imp (Conj (App (Var 2) (Var 1)) (Var 1 \<le>\<^sub>p Var 0))
            (App (Var 2) (Var 0)))))"

definition caie_GLBC_op :: oterm where
  "caie_GLBC_op =
    Lam caie_classifier_ty
      (Forall caie_prop_class_ty
        (Imp
          (Forall caie_prop_ty
            (Imp (App (Var 1) (Var 0)) (App (Var 2) (Var 0))))
          (Forall caie_prop_ty
            (Imp (App (App caie_GLB_op (Var 1)) (Var 0)) (App (Var 2) (Var 0))))))"

definition caie_Comp_op :: oterm where
  "caie_Comp_op =
    Lam caie_classifier_ty
      (Forall caie_prop_ty
        (Disj (App (Var 1) (Var 0)) (App (Var 1) (caie_prop_neg (Var 0)))))"

definition caie_Cons_op :: oterm where
  "caie_Cons_op =
    Lam caie_classifier_ty
      (Neg (App (Var 0) caie_bottom_prop))"

definition caie_MC_op :: oterm where
  "caie_MC_op =
    Lam caie_classifier_ty
      (Conj (Conj (App caie_Comp_op (Var 0)) (App caie_Cons_op (Var 0)))
        (Conj (App caie_UC_op (Var 0)) (App caie_GLBC_op (Var 0))))"

subsection \<open>Haecceities, Names, and projections\<close>

definition caie_Hae_op :: oterm where
  "caie_Hae_op =
    Lam caie_classifier_ty
      (Exists Ind
        (Eq caie_classifier_ty (Var 1)
          (Lam caie_prop_ty (App (Var 0) (Var 1)))))"

definition caie_hae_op :: oterm where
  "caie_hae_op =
    Lam caie_prop_ty
      (Exists Ind (Eq caie_prop_ty (Var 1) (caie_heq (Var 0))))"

definition caie_NH_op :: oterm where
  "caie_NH_op =
    Lam caie_classifier_ty
      (Neg (Exists Ind (App (Var 1) (caie_heq (Var 0)))))"

definition caie_AH_op :: oterm where
  "caie_AH_op =
    Lam caie_classifier_ty
      (Forall Ind (App (Var 1) (caie_prop_neg (caie_heq (Var 0)))))"

definition caie_AC_op :: oterm where
  "caie_AC_op =
    Lam caie_classifier_ty
      (Forall Ind
        (Imp (App (Var 1) (caie_heq (Var 0)))
          (Forall caie_prop_ty
            (App (Var 2) (Var 0) \<longleftrightarrow>\<^sub>o App (Var 0) (Var 1)))))"

definition caie_HP_op :: oterm where
  "caie_HP_op =
    Lam caie_classifier_ty
      (Forall Ind
        (Imp (App (Var 1) (caie_heq (Var 0)))
          (\<box>\<^sub>o App (Var 1) (caie_heq (Var 0)))))"

definition caie_NHP_op :: oterm where
  "caie_NHP_op =
    Lam caie_classifier_ty
      (Forall Ind
        (Imp (Neg (App (Var 1) (caie_heq (Var 0))))
          (\<box>\<^sub>o Neg (App (Var 1) (caie_heq (Var 0))))))"

definition caie_ACF_op :: oterm where
  "caie_ACF_op =
    Lam caie_classifier_ty
      (Forall caie_prop_ty
        (App (Var 1) (Var 0) \<longleftrightarrow>\<^sub>o
          ((Exists Ind (App (Var 2) (caie_heq (Var 0))))
            \<box>\<rightarrow>\<^sub>o App (Var 1) (Var 0))))"

definition caie_PE_op :: oterm where
  "caie_PE_op =
    Lam caie_classifier_ty
      (\<diamond>\<^sub>o (Exists Ind (App (Var 1) (caie_heq (Var 0)))))"

definition caie_Name_op :: oterm where
  "caie_Name_op =
    Lam caie_classifier_ty
      (\<box>\<^sub>o
        (Conj
          (Conj (App caie_MC_op (Var 0)) (App caie_AC_op (Var 0)))
          (Conj (App caie_HP_op (Var 0))
            (Conj (App caie_NHP_op (Var 0)) (App caie_ACF_op (Var 0))))))"

definition caie_WName_op :: oterm where
  "caie_WName_op =
    Lam caie_classifier_ty
      (\<box>\<^sub>o
        (Conj
          (Conj (App caie_MC_op (Var 0)) (App caie_AC_op (Var 0)))
          (Conj (App caie_HP_op (Var 0))
            (Conj (App caie_NHP_op (Var 0)) (App caie_PE_op (Var 0))))))"

definition caie_down_op :: oterm where
  "caie_down_op =
    Lam caie_classifier_ty
      (Lam Ind (App (Var 1) (caie_heq (Var 0))))"

definition caie_up_op :: oterm where
  "caie_up_op =
    Lam caie_prop_ty
      (Lam caie_prop_ty
        ((Exists Ind (Eq caie_prop_ty (Var 2) (caie_heq (Var 0))))
          \<box>\<rightarrow>\<^sub>o
         (Exists Ind (Conj (App (Var 2) (Var 0)) (App (Var 1) (Var 0))))))"

definition caie_phae_op :: oterm where
  "caie_phae_op =
    Lam caie_prop_ty
      (\<box>\<^sub>o
        (Conj
          (\<diamond>\<^sub>o (Exists Ind (Eq caie_prop_ty (Var 1) (caie_heq (Var 0)))))
          (Conj
            (Forall Ind
              (Imp (App (Var 1) (Var 0)) (\<box>\<^sub>o App (Var 1) (Var 0))))
            (Forall Ind
              (Imp (Neg (App (Var 1) (Var 0))) (\<box>\<^sub>o Neg (App (Var 1) (Var 0))))))))"

definition caie_dsim_op :: oterm where
  "caie_dsim_op =
    Lam caie_classifier_ty
      (Lam caie_classifier_ty
        (Eq caie_prop_ty (App caie_down_op (Var 1)) (App caie_down_op (Var 0))))"

definition caie_up_body :: "oterm \<Rightarrow> oterm \<Rightarrow> oterm" where
  "caie_up_body P R =
    ((Exists Ind (Eq caie_prop_ty (shift P) (caie_heq (Var 0))))
      \<box>\<rightarrow>\<^sub>o
     (Exists Ind (Conj (App (shift P) (Var 0)) (App (shift R) (Var 0)))))"

subsection \<open>Applied abbreviations\<close>

abbreviation caie_GLB :: "oterm \<Rightarrow> oterm \<Rightarrow> oterm" where
  "caie_GLB Z P \<equiv> App (App caie_GLB_op Z) P"

abbreviation caie_NS :: "oterm \<Rightarrow> oterm" where
  "caie_NS Q \<equiv> App caie_NS_op Q"

abbreviation caie_UC :: "oterm \<Rightarrow> oterm" where
  "caie_UC Q \<equiv> App caie_UC_op Q"

abbreviation caie_GLBC :: "oterm \<Rightarrow> oterm" where
  "caie_GLBC Q \<equiv> App caie_GLBC_op Q"

abbreviation caie_Comp :: "oterm \<Rightarrow> oterm" where
  "caie_Comp Q \<equiv> App caie_Comp_op Q"

abbreviation caie_Cons :: "oterm \<Rightarrow> oterm" where
  "caie_Cons Q \<equiv> App caie_Cons_op Q"

abbreviation caie_MC :: "oterm \<Rightarrow> oterm" where
  "caie_MC Q \<equiv> App caie_MC_op Q"

abbreviation caie_Hae :: "oterm \<Rightarrow> oterm" where
  "caie_Hae Q \<equiv> App caie_Hae_op Q"

abbreviation caie_hae :: "oterm \<Rightarrow> oterm" where
  "caie_hae P \<equiv> App caie_hae_op P"

abbreviation caie_NH :: "oterm \<Rightarrow> oterm" where
  "caie_NH Q \<equiv> App caie_NH_op Q"

abbreviation caie_AH :: "oterm \<Rightarrow> oterm" where
  "caie_AH Q \<equiv> App caie_AH_op Q"

abbreviation caie_AC :: "oterm \<Rightarrow> oterm" where
  "caie_AC Q \<equiv> App caie_AC_op Q"

abbreviation caie_HP :: "oterm \<Rightarrow> oterm" where
  "caie_HP Q \<equiv> App caie_HP_op Q"

abbreviation caie_NHP :: "oterm \<Rightarrow> oterm" where
  "caie_NHP Q \<equiv> App caie_NHP_op Q"

abbreviation caie_ACF :: "oterm \<Rightarrow> oterm" where
  "caie_ACF Q \<equiv> App caie_ACF_op Q"

abbreviation caie_PE :: "oterm \<Rightarrow> oterm" where
  "caie_PE Q \<equiv> App caie_PE_op Q"

abbreviation caie_Name :: "oterm \<Rightarrow> oterm" where
  "caie_Name Q \<equiv> App caie_Name_op Q"

abbreviation caie_WName :: "oterm \<Rightarrow> oterm" where
  "caie_WName Q \<equiv> App caie_WName_op Q"

abbreviation caie_down :: "oterm \<Rightarrow> oterm" ("_\<^sup>\<down>\<^sub>c" [80] 80) where
  "Q\<^sup>\<down>\<^sub>c \<equiv> App caie_down_op Q"

abbreviation caie_up :: "oterm \<Rightarrow> oterm" ("_\<^sup>\<up>\<^sub>c" [80] 80) where
  "P\<^sup>\<up>\<^sub>c \<equiv> App caie_up_op P"

abbreviation caie_phae :: "oterm \<Rightarrow> oterm" where
  "caie_phae P \<equiv> App caie_phae_op P"

abbreviation caie_dsim :: "oterm \<Rightarrow> oterm \<Rightarrow> oterm" (infix "\<sim>\<^sub>\<down>c" 52) where
  "Q \<sim>\<^sub>\<down>c Z \<equiv> App (App caie_dsim_op Q) Z"

subsection \<open>Typing facts\<close>

named_theorems caie_type_defs
declare caie_prop_ty_def[caie_type_defs] caie_classifier_ty_def[caie_type_defs]
  caie_prop_class_ty_def[caie_type_defs] caie_classifier_class_ty_def[caie_type_defs]
  pred_ty_def[caie_type_defs] prop_bin_ty_def[caie_type_defs]

named_theorems caie_term_defs
declare caie_cf_const_def[caie_term_defs] ObjCF_def[caie_term_defs]
  caie_heq_def[caie_term_defs] caie_prop_neg_def[caie_term_defs]
  caie_top_prop_def[caie_term_defs] caie_bottom_prop_def[caie_term_defs]
  caie_exists_prop_def[caie_term_defs] caie_prop_entails_def[caie_term_defs]
  caie_GLB_op_def[caie_term_defs] caie_NS_op_def[caie_term_defs]
  caie_UC_op_def[caie_term_defs] caie_GLBC_op_def[caie_term_defs]
  caie_Comp_op_def[caie_term_defs] caie_Cons_op_def[caie_term_defs]
  caie_MC_op_def[caie_term_defs] caie_Hae_op_def[caie_term_defs]
  caie_hae_op_def[caie_term_defs] caie_NH_op_def[caie_term_defs]
  caie_AH_op_def[caie_term_defs] caie_AC_op_def[caie_term_defs]
  caie_HP_op_def[caie_term_defs] caie_NHP_op_def[caie_term_defs]
  caie_ACF_op_def[caie_term_defs] caie_PE_op_def[caie_term_defs]
  caie_Name_op_def[caie_term_defs] caie_WName_op_def[caie_term_defs]
  caie_down_op_def[caie_term_defs] caie_up_op_def[caie_term_defs]
  caie_phae_op_def[caie_term_defs] caie_dsim_op_def[caie_term_defs]
  caie_up_body_def[caie_term_defs]
  ObjBox_def[caie_term_defs] ObjDiamond_def[caie_term_defs]
  ObjTrue_def[caie_term_defs] ObjFalse_def[caie_term_defs]
  shift_def[caie_term_defs]

lemma typed_caie_cf_const:
  "\<Gamma> \<turnstile> caie_cf_const : prop_bin_ty"
  by (auto simp: caie_term_defs)

lemma typed_ObjCF:
  assumes "\<Gamma> \<turnstile> A : Prop" and "\<Gamma> \<turnstile> B : Prop"
  shows "\<Gamma> \<turnstile> ObjCF A B : Prop"
  using assms typed_caie_cf_const
  by (auto simp: ObjCF_def prop_bin_ty_def)

lemma typed_caie_heq:
  assumes "\<Gamma> \<turnstile> x : Ind"
  shows "\<Gamma> \<turnstile> caie_heq x : caie_prop_ty"
proof -
  have "Ind # \<Gamma> \<turnstile> shift x : Ind"
    using assms by (rule weakening_front)
  then show ?thesis
    unfolding caie_heq_def caie_prop_ty_def pred_ty_def
    by (intro has_type.Lam has_type.Eq has_type.Var) auto
qed

lemma typed_caie_prop_neg:
  assumes "\<Gamma> \<turnstile> P : caie_prop_ty"
  shows "\<Gamma> \<turnstile> caie_prop_neg P : caie_prop_ty"
proof -
  have "Ind # \<Gamma> \<turnstile> shift P : caie_prop_ty"
    using assms by (rule weakening_front)
  then show ?thesis
    unfolding caie_prop_neg_def caie_prop_ty_def pred_ty_def
    by (intro has_type.Lam has_type.Neg has_type.App has_type.Var) auto
qed

lemma typed_caie_top_prop:
  "\<Gamma> \<turnstile> caie_top_prop : caie_prop_ty"
  unfolding caie_top_prop_def caie_prop_ty_def pred_ty_def
  by (auto intro: typed_ObjTrue)

lemma typed_caie_bottom_prop:
  "\<Gamma> \<turnstile> caie_bottom_prop : caie_prop_ty"
  unfolding caie_bottom_prop_def caie_prop_ty_def pred_ty_def
  by (auto intro: typed_ObjFalse)

lemma typed_caie_exists_prop:
  "\<Gamma> \<turnstile> caie_exists_prop : caie_prop_ty"
  unfolding caie_exists_prop_def caie_prop_ty_def pred_ty_def
  by (intro has_type.Lam has_type.Exists has_type.Eq has_type.Var) auto

lemma typed_caie_prop_entails:
  assumes "\<Gamma> \<turnstile> P : caie_prop_ty" and "\<Gamma> \<turnstile> R : caie_prop_ty"
  shows "\<Gamma> \<turnstile> caie_prop_entails P R : Prop"
proof -
  have P_shift: "Ind # \<Gamma> \<turnstile> shift P : caie_prop_ty"
    using assms(1) by (rule weakening_front)
  have R_shift: "Ind # \<Gamma> \<turnstile> shift R : caie_prop_ty"
    using assms(2) by (rule weakening_front)
  have P_app: "Ind # \<Gamma> \<turnstile> App (shift P) (Var 0) : Prop"
    using P_shift unfolding caie_prop_ty_def pred_ty_def by auto
  have R_app: "Ind # \<Gamma> \<turnstile> App (shift R) (Var 0) : Prop"
    using R_shift unfolding caie_prop_ty_def pred_ty_def by auto
  have "Ind # \<Gamma> \<turnstile> Imp (App (shift P) (Var 0)) (App (shift R) (Var 0)) : Prop"
    using P_app R_app by auto
  then show ?thesis
    unfolding caie_prop_entails_def by (auto intro: typed_ObjBox)
qed

lemma typed_caie_GLB_op:
  "\<Gamma> \<turnstile> caie_GLB_op : caie_prop_class_ty \<rightarrow>\<^sub>o caie_prop_ty \<rightarrow>\<^sub>o Prop"
  by (rule infer_type_sound)
    (simp add: caie_term_defs caie_type_defs lookup_def)

lemma typed_caie_NS_op:
  "\<Gamma> \<turnstile> caie_NS_op : caie_classifier_class_ty"
  by (rule infer_type_sound)
    (simp add: caie_term_defs caie_type_defs lookup_def)

lemma typed_caie_UC_op:
  "\<Gamma> \<turnstile> caie_UC_op : caie_classifier_class_ty"
  by (rule infer_type_sound)
    (simp add: caie_term_defs caie_type_defs lookup_def)

lemma typed_caie_GLBC_op:
  "\<Gamma> \<turnstile> caie_GLBC_op : caie_classifier_class_ty"
  by (rule infer_type_sound)
    (simp add: caie_term_defs caie_type_defs lookup_def)

lemma typed_caie_Comp_op:
  "\<Gamma> \<turnstile> caie_Comp_op : caie_classifier_class_ty"
  by (rule infer_type_sound)
    (simp add: caie_term_defs caie_type_defs lookup_def)

lemma typed_caie_Cons_op:
  "\<Gamma> \<turnstile> caie_Cons_op : caie_classifier_class_ty"
  by (rule infer_type_sound)
    (simp add: caie_term_defs caie_type_defs lookup_def)

lemma typed_caie_MC_op:
  "\<Gamma> \<turnstile> caie_MC_op : caie_classifier_class_ty"
  by (rule infer_type_sound)
    (simp add: caie_term_defs caie_type_defs lookup_def)

lemma typed_caie_Hae_op:
  "\<Gamma> \<turnstile> caie_Hae_op : caie_classifier_class_ty"
  by (rule infer_type_sound)
    (simp add: caie_term_defs caie_type_defs lookup_def)

lemma typed_caie_hae_op:
  "\<Gamma> \<turnstile> caie_hae_op : caie_prop_class_ty"
  by (rule infer_type_sound)
    (simp add: caie_term_defs caie_type_defs lookup_def)

lemma typed_caie_NH_op:
  "\<Gamma> \<turnstile> caie_NH_op : caie_classifier_class_ty"
  by (rule infer_type_sound)
    (simp add: caie_term_defs caie_type_defs lookup_def)

lemma typed_caie_AH_op:
  "\<Gamma> \<turnstile> caie_AH_op : caie_classifier_class_ty"
  by (rule infer_type_sound)
    (simp add: caie_term_defs caie_type_defs lookup_def)

lemma typed_caie_AC_op:
  "\<Gamma> \<turnstile> caie_AC_op : caie_classifier_class_ty"
  by (rule infer_type_sound)
    (simp add: caie_term_defs caie_type_defs lookup_def)

lemma typed_caie_HP_op:
  "\<Gamma> \<turnstile> caie_HP_op : caie_classifier_class_ty"
  by (rule infer_type_sound)
    (simp add: caie_term_defs caie_type_defs lookup_def)

lemma typed_caie_NHP_op:
  "\<Gamma> \<turnstile> caie_NHP_op : caie_classifier_class_ty"
  by (rule infer_type_sound)
    (simp add: caie_term_defs caie_type_defs lookup_def)

lemma typed_caie_ACF_op:
  "\<Gamma> \<turnstile> caie_ACF_op : caie_classifier_class_ty"
  by (rule infer_type_sound)
    (simp add: caie_term_defs caie_type_defs lookup_def)

lemma typed_caie_PE_op:
  "\<Gamma> \<turnstile> caie_PE_op : caie_classifier_class_ty"
  by (rule infer_type_sound)
    (simp add: caie_term_defs caie_type_defs lookup_def)

lemma typed_caie_Name_op:
  "\<Gamma> \<turnstile> caie_Name_op : caie_classifier_class_ty"
  by (rule infer_type_sound)
    (simp add: caie_term_defs caie_type_defs lookup_def)

lemma typed_caie_WName_op:
  "\<Gamma> \<turnstile> caie_WName_op : caie_classifier_class_ty"
  by (rule infer_type_sound)
    (simp add: caie_term_defs caie_type_defs lookup_def)

lemma typed_caie_down_op:
  "\<Gamma> \<turnstile> caie_down_op : caie_classifier_ty \<rightarrow>\<^sub>o caie_prop_ty"
  by (rule infer_type_sound)
    (simp add: caie_term_defs caie_type_defs lookup_def)

lemma typed_caie_up_op:
  "\<Gamma> \<turnstile> caie_up_op : caie_prop_ty \<rightarrow>\<^sub>o caie_classifier_ty"
  by (rule infer_type_sound)
    (simp add: caie_term_defs caie_type_defs lookup_def)

lemma typed_caie_phae_op:
  "\<Gamma> \<turnstile> caie_phae_op : caie_prop_class_ty"
  by (rule infer_type_sound)
    (simp add: caie_term_defs caie_type_defs lookup_def)

lemma typed_caie_dsim_op:
  "\<Gamma> \<turnstile> caie_dsim_op : caie_classifier_ty \<rightarrow>\<^sub>o caie_classifier_ty \<rightarrow>\<^sub>o Prop"
  by (rule infer_type_sound)
    (simp add: caie_term_defs caie_type_defs lookup_def)

lemma typed_caie_Name:
  assumes "\<Gamma> \<turnstile> Q : caie_classifier_ty"
  shows "\<Gamma> \<turnstile> caie_Name Q : Prop"
  using typed_caie_Name_op assms
  by (auto simp: caie_classifier_class_ty_def pred_ty_def)

lemma typed_caie_WName:
  assumes "\<Gamma> \<turnstile> Q : caie_classifier_ty"
  shows "\<Gamma> \<turnstile> caie_WName Q : Prop"
  using typed_caie_WName_op assms
  by (auto simp: caie_classifier_class_ty_def pred_ty_def)

lemma typed_caie_down:
  assumes "\<Gamma> \<turnstile> Q : caie_classifier_ty"
  shows "\<Gamma> \<turnstile> Q\<^sup>\<down>\<^sub>c : caie_prop_ty"
  using typed_caie_down_op assms by auto

lemma typed_caie_up:
  assumes "\<Gamma> \<turnstile> P : caie_prop_ty"
  shows "\<Gamma> \<turnstile> P\<^sup>\<up>\<^sub>c : caie_classifier_ty"
  using typed_caie_up_op assms by auto

lemma typed_caie_phae:
  assumes "\<Gamma> \<turnstile> P : caie_prop_ty"
  shows "\<Gamma> \<turnstile> caie_phae P : Prop"
  using typed_caie_phae_op assms
  by (auto simp: caie_prop_class_ty_def pred_ty_def)

lemma typed_caie_dsim:
  assumes "\<Gamma> \<turnstile> Q : caie_classifier_ty" and "\<Gamma> \<turnstile> Z : caie_classifier_ty"
  shows "\<Gamma> \<turnstile> Q \<sim>\<^sub>\<down>c Z : Prop"
  using typed_caie_dsim_op assms by auto

lemma typed_caie_prop_class_app:
  assumes "\<Gamma> \<turnstile> F : caie_prop_class_ty"
    and "\<Gamma> \<turnstile> P : caie_prop_ty"
  shows "\<Gamma> \<turnstile> App F P : Prop"
  using assms by (auto simp: caie_prop_class_ty_def)

lemma typed_caie_classifier_class_app:
  assumes "\<Gamma> \<turnstile> F : caie_classifier_class_ty"
    and "\<Gamma> \<turnstile> Q : caie_classifier_ty"
  shows "\<Gamma> \<turnstile> App F Q : Prop"
  using assms by (auto simp: caie_classifier_class_ty_def)

lemma typed_caie_GLB:
  assumes "\<Gamma> \<turnstile> Z : caie_prop_class_ty"
    and "\<Gamma> \<turnstile> P : caie_prop_ty"
  shows "\<Gamma> \<turnstile> caie_GLB Z P : Prop"
  using typed_caie_GLB_op assms by auto

lemma typed_caie_NS:
  assumes "\<Gamma> \<turnstile> Q : caie_classifier_ty"
  shows "\<Gamma> \<turnstile> caie_NS Q : Prop"
  using typed_caie_NS_op assms by (rule typed_caie_classifier_class_app)

lemma typed_caie_UC:
  assumes "\<Gamma> \<turnstile> Q : caie_classifier_ty"
  shows "\<Gamma> \<turnstile> caie_UC Q : Prop"
  using typed_caie_UC_op assms by (rule typed_caie_classifier_class_app)

lemma typed_caie_GLBC:
  assumes "\<Gamma> \<turnstile> Q : caie_classifier_ty"
  shows "\<Gamma> \<turnstile> caie_GLBC Q : Prop"
  using typed_caie_GLBC_op assms by (rule typed_caie_classifier_class_app)

lemma typed_caie_Comp:
  assumes "\<Gamma> \<turnstile> Q : caie_classifier_ty"
  shows "\<Gamma> \<turnstile> caie_Comp Q : Prop"
  using typed_caie_Comp_op assms by (rule typed_caie_classifier_class_app)

lemma typed_caie_Cons:
  assumes "\<Gamma> \<turnstile> Q : caie_classifier_ty"
  shows "\<Gamma> \<turnstile> caie_Cons Q : Prop"
  using typed_caie_Cons_op assms by (rule typed_caie_classifier_class_app)

lemma typed_caie_MC:
  assumes "\<Gamma> \<turnstile> Q : caie_classifier_ty"
  shows "\<Gamma> \<turnstile> caie_MC Q : Prop"
  using typed_caie_MC_op assms by (rule typed_caie_classifier_class_app)

lemma typed_caie_Hae:
  assumes "\<Gamma> \<turnstile> Q : caie_classifier_ty"
  shows "\<Gamma> \<turnstile> caie_Hae Q : Prop"
  using typed_caie_Hae_op assms by (rule typed_caie_classifier_class_app)

lemma typed_caie_hae:
  assumes "\<Gamma> \<turnstile> P : caie_prop_ty"
  shows "\<Gamma> \<turnstile> caie_hae P : Prop"
  using typed_caie_hae_op assms by (rule typed_caie_prop_class_app)

lemma typed_caie_NH:
  assumes "\<Gamma> \<turnstile> Q : caie_classifier_ty"
  shows "\<Gamma> \<turnstile> caie_NH Q : Prop"
  using typed_caie_NH_op assms by (rule typed_caie_classifier_class_app)

lemma typed_caie_AH:
  assumes "\<Gamma> \<turnstile> Q : caie_classifier_ty"
  shows "\<Gamma> \<turnstile> caie_AH Q : Prop"
  using typed_caie_AH_op assms by (rule typed_caie_classifier_class_app)

lemma typed_caie_AC:
  assumes "\<Gamma> \<turnstile> Q : caie_classifier_ty"
  shows "\<Gamma> \<turnstile> caie_AC Q : Prop"
  using typed_caie_AC_op assms by (rule typed_caie_classifier_class_app)

lemma typed_caie_HP:
  assumes "\<Gamma> \<turnstile> Q : caie_classifier_ty"
  shows "\<Gamma> \<turnstile> caie_HP Q : Prop"
  using typed_caie_HP_op assms by (rule typed_caie_classifier_class_app)

lemma typed_caie_NHP:
  assumes "\<Gamma> \<turnstile> Q : caie_classifier_ty"
  shows "\<Gamma> \<turnstile> caie_NHP Q : Prop"
  using typed_caie_NHP_op assms by (rule typed_caie_classifier_class_app)

lemma typed_caie_ACF:
  assumes "\<Gamma> \<turnstile> Q : caie_classifier_ty"
  shows "\<Gamma> \<turnstile> caie_ACF Q : Prop"
  using typed_caie_ACF_op assms by (rule typed_caie_classifier_class_app)

lemma typed_caie_PE:
  assumes "\<Gamma> \<turnstile> Q : caie_classifier_ty"
  shows "\<Gamma> \<turnstile> caie_PE Q : Prop"
  using typed_caie_PE_op assms by (rule typed_caie_classifier_class_app)

lemma typed_caie_up_body:
  assumes "\<Gamma> \<turnstile> P : caie_prop_ty"
    and "\<Gamma> \<turnstile> R : caie_prop_ty"
  shows "\<Gamma> \<turnstile> caie_up_body P R : Prop"
proof -
  have P_shift: "Ind # \<Gamma> \<turnstile> shift P : caie_prop_ty"
    using assms(1) by (rule weakening_front)
  have R_shift: "Ind # \<Gamma> \<turnstile> shift R : caie_prop_ty"
    using assms(2) by (rule weakening_front)
  have var0_type: "Ind # \<Gamma> \<turnstile> Var 0 : Ind"
    by auto
  have heq_var_type: "Ind # \<Gamma> \<turnstile> caie_heq (Var 0) : caie_prop_ty"
    using var0_type by (rule typed_caie_heq)
  have antecedent_body:
      "Ind # \<Gamma> \<turnstile> Eq caie_prop_ty (shift P) (caie_heq (Var 0)) : Prop"
    using P_shift heq_var_type by auto
  have antecedent: "\<Gamma> \<turnstile>
      Exists Ind (Eq caie_prop_ty (shift P) (caie_heq (Var 0))) : Prop"
    using antecedent_body by auto
  have P_app: "Ind # \<Gamma> \<turnstile> App (shift P) (Var 0) : Prop"
    using P_shift var0_type by (auto simp: caie_prop_ty_def pred_ty_def)
  have R_app: "Ind # \<Gamma> \<turnstile> App (shift R) (Var 0) : Prop"
    using R_shift var0_type by (auto simp: caie_prop_ty_def pred_ty_def)
  have consequent_body: "Ind # \<Gamma> \<turnstile>
      Conj (App (shift P) (Var 0)) (App (shift R) (Var 0)) : Prop"
    using P_app R_app by auto
  have consequent: "\<Gamma> \<turnstile>
      Exists Ind (Conj (App (shift P) (Var 0)) (App (shift R) (Var 0))) : Prop"
    using consequent_body by auto
  show ?thesis
    unfolding caie_up_body_def
    using antecedent consequent by (rule typed_ObjCF)
qed

subsection \<open>Definitional conversion facts\<close>

text \<open>
  These lemmas make the conservative Caie definitions available at the proof
  level.  The first says that the individual haecceity term \<open>heq x\<close>, applied
  to \<open>y\<close>, beta-reduces to object-language identity \<open>y = x\<close>.  The second is
  Caie's down-projection equation: applying \<open>Q\<^sup>\<down>\<^sub>c\<close> to an individual is
  equivalent to applying the classifier \<open>Q\<close> to that individual's haecceity.
\<close>

lemma caie_up_op_as_body:
  "caie_up_op = Lam caie_prop_ty (Lam caie_prop_ty (caie_up_body (Var 1) (Var 0)))"
proof -
  have two: "(2::nat) = Suc (Suc 0)"
    by simp
  show ?thesis
    by (simp add: caie_up_op_def caie_up_body_def shift_def two)
qed

lemma subst_caie_cf_const[simp]:
  "subst s caie_cf_const = caie_cf_const"
  by (simp add: caie_cf_const_def)

lemma caie_subst_cong:
  assumes "\<And>n. s n = t n"
  shows "subst s M = subst t M"
  using assms
proof (induction M arbitrary: s t)
  case (Var n)
  then show ?case
    by simp
next
  case (Const c \<tau>)
  then show ?case
    by simp
next
  case (App M P)
  then show ?case
    by simp
next
  case (Lam \<rho> M)
  have lift_eq: "\<And>n. lift_subst s n = lift_subst t n"
    using Lam.prems by (case_tac n; simp)
  have "subst (lift_subst s) M = subst (lift_subst t) M"
    using lift_eq by (rule Lam.IH)
  then show ?case
    by simp
next
  case (Eq \<rho> M P)
  then show ?case
    by simp
next
  case (Neg A)
  then show ?case
    by simp
next
  case (Conj A B)
  then show ?case
    by simp
next
  case (Disj A B)
  then show ?case
    by simp
next
  case (Imp A B)
  then show ?case
    by simp
next
  case (Forall \<rho> M)
  have lift_eq: "\<And>n. lift_subst s n = lift_subst t n"
    using Forall.prems by (case_tac n; simp)
  have "subst (lift_subst s) M = subst (lift_subst t) M"
    using lift_eq by (rule Forall.IH)
  then show ?case
    by simp
next
  case (Exists \<rho> M)
  have lift_eq: "\<And>n. lift_subst s n = lift_subst t n"
    using Exists.prems by (case_tac n; simp)
  have "subst (lift_subst s) M = subst (lift_subst t) M"
    using lift_eq by (rule Exists.IH)
  then show ?case
    by simp
qed

lemma caie_subst_rename:
  "subst s (rename r M) = subst (s \<circ> r) M"
proof (induction M arbitrary: s r)
  case (Lam \<rho> M)
  have "subst (lift_subst s) (rename (lift_ren r) M) =
      subst (lift_subst s \<circ> lift_ren r) M"
    by (rule Lam.IH)
  also have "... = subst (lift_subst (s \<circ> r)) M"
    by (rule caie_subst_cong) (case_tac n; simp)
  finally show ?case
    by (simp add: comp_def)
next
  case (Forall \<rho> M)
  have "subst (lift_subst s) (rename (lift_ren r) M) =
      subst (lift_subst s \<circ> lift_ren r) M"
    by (rule Forall.IH)
  also have "... = subst (lift_subst (s \<circ> r)) M"
    by (rule caie_subst_cong) (case_tac n; simp)
  finally show ?case
    by (simp add: comp_def)
next
  case (Exists \<rho> M)
  have "subst (lift_subst s) (rename (lift_ren r) M) =
      subst (lift_subst s \<circ> lift_ren r) M"
    by (rule Exists.IH)
  also have "... = subst (lift_subst (s \<circ> r)) M"
    by (rule caie_subst_cong) (case_tac n; simp)
    finally show ?case
      by (simp add: comp_def)
  qed simp_all

lemma caie_lift_subst_Var[simp]:
  "lift_subst Var = Var"
  by (rule ext) (case_tac x; simp)

lemma caie_subst_Var[simp]:
  "subst Var M = M"
  by (induction M) simp_all

lemma subst_Suc_Var:
  "subst (\<lambda>n. Var (Suc n)) M = shift M"
proof -
  have map_eq: "subst (\<lambda>n. Var (Suc n)) M = subst (Var \<circ> Suc) M"
    by (rule caie_subst_cong) simp
  have shifted_eq: "shift M = subst (Var \<circ> Suc) M"
    unfolding shift_def using caie_subst_rename[of Var Suc M] by simp
  show ?thesis
    using map_eq shifted_eq by simp
qed

lemma subst_lift_case_shift_shift:
  "subst (lift_subst (case_nat R Var)) (shift (shift P)) = shift P"
proof -
  let ?s = "lift_subst (case_nat R Var)"
  have "subst ?s (shift (shift P)) = subst (?s \<circ> Suc) (shift P)"
    unfolding shift_def by (simp add: caie_subst_rename)
  also have "... = subst ((?s \<circ> Suc) \<circ> Suc) P"
    unfolding shift_def by (simp add: caie_subst_rename)
  also have "... = subst (\<lambda>n. Var (Suc n)) P"
    by (rule caie_subst_cong) simp
  also have "... = shift P"
    by (rule subst_Suc_Var)
  finally show ?thesis .
qed

lemma subst_lift_case_shift_Var0:
  "subst (lift_subst (case_nat R Var)) (shift (Var 0)) = shift R"
  by (simp add: shift_def)

lemma subst_lift_lift_case_shift_Var0:
  "subst (lift_subst (lift_subst (case_nat R Var))) (shift (Var 0)) = shift (Var 0)"
  by (simp add: shift_def)

lemma subst0_caie_up_body_shift_Var0:
  "subst0 R (caie_up_body (shift P) (Var 0)) = caie_up_body P R"
  by (simp add: caie_up_body_def ObjCF_def subst0_def caie_heq_def
      subst_lift_case_shift_shift subst_lift_case_shift_Var0
      subst_lift_lift_case_shift_Var0)

lemma subst_lift_caie_up_body_Var1_Var0:
  "subst (lift_subst (case_nat P Var)) (caie_up_body (Var (Suc 0)) (Var 0)) =
    caie_up_body (shift P) (Var 0)"
  by (simp add: caie_up_body_def ObjCF_def caie_heq_def shift_def)

lemma subst_caie_down_op[simp]:
  "subst s caie_down_op = caie_down_op"
  by (simp add: caie_down_op_def caie_heq_def shift_def)

lemma subst_caie_up_op[simp]:
  "subst s caie_up_op = caie_up_op"
  by (simp add: caie_up_op_def caie_up_body_def ObjCF_def caie_heq_def
      shift_def eval_nat_numeral)

lemma subst_caie_Name_op[simp]:
  "subst s caie_Name_op = caie_Name_op"
  by (simp add: caie_Name_op_def caie_term_defs caie_type_defs shift_def
      eval_nat_numeral)

lemma subst_caie_WName_op[simp]:
  "subst s caie_WName_op = caie_WName_op"
  by (simp add: caie_WName_op_def caie_term_defs caie_type_defs shift_def
      eval_nat_numeral)

lemma subst_caie_Hae_op[simp]:
  "subst s caie_Hae_op = caie_Hae_op"
  by (simp add: caie_Hae_op_def caie_term_defs caie_type_defs shift_def
      eval_nat_numeral)

lemma subst_caie_hae_op[simp]:
  "subst s caie_hae_op = caie_hae_op"
  by (simp add: caie_hae_op_def caie_heq_def shift_def)

lemma rename_caie_up_op[simp]:
  "rename r caie_up_op = caie_up_op"
  by (simp add: caie_up_op_def caie_up_body_def ObjCF_def caie_heq_def
      caie_cf_const_def shift_def eval_nat_numeral)

lemma rename_caie_down_op[simp]:
  "rename r caie_down_op = caie_down_op"
  by (simp add: caie_down_op_def caie_heq_def shift_def)

lemma rename_caie_phae_op[simp]:
  "rename r caie_phae_op = caie_phae_op"
  by (simp add: caie_phae_op_def ObjBox_def ObjDiamond_def ObjTrue_def
      ObjFalse_def caie_heq_def shift_def eval_nat_numeral)

lemma rename_caie_Name_op[simp]:
  "rename r caie_Name_op = caie_Name_op"
  by (simp add: caie_Name_op_def caie_term_defs caie_type_defs shift_def
      eval_nat_numeral)

lemma rename_caie_WName_op[simp]:
  "rename r caie_WName_op = caie_WName_op"
  by (simp add: caie_WName_op_def caie_term_defs caie_type_defs shift_def
      eval_nat_numeral)

lemma rename_caie_Hae_op[simp]:
  "rename r caie_Hae_op = caie_Hae_op"
  by (simp add: caie_Hae_op_def caie_term_defs caie_type_defs shift_def
      eval_nat_numeral)

lemma rename_caie_hae_op[simp]:
  "rename r caie_hae_op = caie_hae_op"
  by (simp add: caie_hae_op_def caie_heq_def shift_def)

lemma shift_caie_phae[simp]:
  "shift (caie_phae P) = caie_phae (shift P)"
  by (simp add: shift_def)

lemma shift_caie_hae[simp]:
  "shift (caie_hae P) = caie_hae (shift P)"
  by (simp add: shift_def)

lemma shift_caie_WName[simp]:
  "shift (caie_WName Q) = caie_WName (shift Q)"
  by (simp add: shift_def)

lemma shift_caie_Hae[simp]:
  "shift (caie_Hae Q) = caie_Hae (shift Q)"
  by (simp add: shift_def)

lemma subst_lift_caie_dsim_body_Var1_Var0:
  "subst (lift_subst (case_nat Q Var))
    (Eq caie_prop_ty ((Var (Suc 0))\<^sup>\<down>\<^sub>c) ((Var 0)\<^sup>\<down>\<^sub>c)) =
    Eq caie_prop_ty ((shift Q)\<^sup>\<down>\<^sub>c) ((Var 0)\<^sup>\<down>\<^sub>c)"
  by (simp add: caie_down_op_def caie_heq_def shift_def)

lemma subst0_caie_dsim_body_shift_Var0:
  "subst0 Z (Eq caie_prop_ty ((shift Q)\<^sup>\<down>\<^sub>c) ((Var 0)\<^sup>\<down>\<^sub>c)) =
    Eq caie_prop_ty (Q\<^sup>\<down>\<^sub>c) (Z\<^sup>\<down>\<^sub>c)"
  by (simp add: subst0_def)

lemma subst_lift_caie_heq_Var0[simp]:
  "subst (lift_subst s) (caie_heq (Var 0)) = caie_heq (Var 0)"
  by (simp add: caie_heq_def shift_def)

lemma subst_caie_heq_Var0[simp]:
  "subst (case_nat x Var) (caie_heq (Var 0)) = caie_heq x"
  by (simp add: caie_heq_def shift_def)

lemma subst0_caie_heq_Var0[simp]:
  "subst0 x (caie_heq (Var 0)) = caie_heq x"
  by (simp add: subst0_def)

lemma beta_eta_equiv_Conj_left:
  assumes eqv: "beta_eta_equiv \<Gamma> Prop A B"
    and C: "\<Gamma> \<turnstile> C : Prop"
  shows "beta_eta_equiv \<Gamma> Prop (Conj A C) (Conj B C)"
proof -
  have aux: "\<And>\<Delta> \<tau> A B C.
    beta_eta_equiv \<Delta> \<tau> A B \<Longrightarrow> \<tau> = Prop \<Longrightarrow> \<Delta> \<turnstile> C : Prop \<Longrightarrow>
      beta_eta_equiv \<Delta> Prop (Conj A C) (Conj B C)"
  proof -
    fix \<Delta> \<tau> A B C
    assume e: "beta_eta_equiv \<Delta> \<tau> A B"
      and tau: "\<tau> = Prop"
      and C_type: "\<Delta> \<turnstile> C : Prop"
    show "beta_eta_equiv \<Delta> Prop (Conj A C) (Conj B C)"
      using e tau C_type
    proof (induction arbitrary: C)
      case (Refl \<Delta> M \<tau>)
      have M_type: "\<Delta> \<turnstile> M : Prop"
        using Refl.hyps Refl.prems(1) by simp
      show ?case
        using M_type Refl.prems(2) by (intro beta_eta_equiv.Refl has_type.Conj)
    next
      case (Beta \<Delta> M \<tau> N)
      have M_type: "\<Delta> \<turnstile> M : Prop"
        using Beta.hyps(1) Beta.prems(1) by simp
      have N_type: "\<Delta> \<turnstile> N : Prop"
        using Beta.hyps(2) Beta.prems(1) by simp
      have step: "compatible_step beta_contract (Conj M C) (Conj N C)"
        using Beta.hyps(3) by (rule compatible_step.Conj_left)
      show ?case
        using M_type N_type Beta.prems(2) step
        by (intro beta_eta_equiv.Beta has_type.Conj)
    next
      case (Eta \<Delta> M \<tau> N)
      have M_type: "\<Delta> \<turnstile> M : Prop"
        using Eta.hyps(1) Eta.prems(1) by simp
      have N_type: "\<Delta> \<turnstile> N : Prop"
        using Eta.hyps(2) Eta.prems(1) by simp
      have step: "compatible_step eta_contract (Conj M C) (Conj N C)"
        using Eta.hyps(3) by (rule compatible_step.Conj_left)
      show ?case
        using M_type N_type Eta.prems(2) step
        by (intro beta_eta_equiv.Eta has_type.Conj)
    next
      case (Sym \<Delta> \<tau> M N)
      have NM: "beta_eta_equiv \<Delta> Prop (Conj N C) (Conj M C)"
        using Sym.IH Sym.prems by blast
      show ?case
        using NM .
    next
      case (Trans \<Delta> \<tau> M N P)
      have MN: "beta_eta_equiv \<Delta> Prop (Conj M C) (Conj N C)"
        using Trans.IH(1) Trans.prems by blast
      have NP: "beta_eta_equiv \<Delta> Prop (Conj N C) (Conj P C)"
        using Trans.IH(2) Trans.prems by blast
      show ?case
        using MN NP by (rule beta_eta_equiv.Trans)
    qed
  qed
  show ?thesis
    using eqv refl C by (rule aux)
qed

lemma beta_eta_equiv_Conj_right:
  assumes C: "\<Gamma> \<turnstile> C : Prop"
    and eqv: "beta_eta_equiv \<Gamma> Prop A B"
  shows "beta_eta_equiv \<Gamma> Prop (Conj C A) (Conj C B)"
proof -
  have aux: "\<And>\<Delta> \<tau> A B C.
    beta_eta_equiv \<Delta> \<tau> A B \<Longrightarrow> \<tau> = Prop \<Longrightarrow> \<Delta> \<turnstile> C : Prop \<Longrightarrow>
      beta_eta_equiv \<Delta> Prop (Conj C A) (Conj C B)"
  proof -
    fix \<Delta> \<tau> A B C
    assume e: "beta_eta_equiv \<Delta> \<tau> A B"
      and tau: "\<tau> = Prop"
      and C_type: "\<Delta> \<turnstile> C : Prop"
    show "beta_eta_equiv \<Delta> Prop (Conj C A) (Conj C B)"
      using e tau C_type
    proof (induction arbitrary: C)
      case (Refl \<Delta> M \<tau>)
      have M_type: "\<Delta> \<turnstile> M : Prop"
        using Refl.hyps Refl.prems(1) by simp
      show ?case
        using Refl.prems(2) M_type by (intro beta_eta_equiv.Refl has_type.Conj)
    next
      case (Beta \<Delta> M \<tau> N)
      have M_type: "\<Delta> \<turnstile> M : Prop"
        using Beta.hyps(1) Beta.prems(1) by simp
      have N_type: "\<Delta> \<turnstile> N : Prop"
        using Beta.hyps(2) Beta.prems(1) by simp
      have step: "compatible_step beta_contract (Conj C M) (Conj C N)"
        using Beta.hyps(3) by (rule compatible_step.Conj_right)
      show ?case
        using Beta.prems(2) M_type N_type step
        by (intro beta_eta_equiv.Beta has_type.Conj)
    next
      case (Eta \<Delta> M \<tau> N)
      have M_type: "\<Delta> \<turnstile> M : Prop"
        using Eta.hyps(1) Eta.prems(1) by simp
      have N_type: "\<Delta> \<turnstile> N : Prop"
        using Eta.hyps(2) Eta.prems(1) by simp
      have step: "compatible_step eta_contract (Conj C M) (Conj C N)"
        using Eta.hyps(3) by (rule compatible_step.Conj_right)
      show ?case
        using Eta.prems(2) M_type N_type step
        by (intro beta_eta_equiv.Eta has_type.Conj)
    next
      case (Sym \<Delta> \<tau> M N)
      have NM: "beta_eta_equiv \<Delta> Prop (Conj C N) (Conj C M)"
        using Sym.IH Sym.prems by blast
      show ?case
        using NM .
    next
      case (Trans \<Delta> \<tau> M N P)
      have MN: "beta_eta_equiv \<Delta> Prop (Conj C M) (Conj C N)"
        using Trans.IH(1) Trans.prems by blast
      have NP: "beta_eta_equiv \<Delta> Prop (Conj C N) (Conj C P)"
        using Trans.IH(2) Trans.prems by blast
      show ?case
        using MN NP by (rule beta_eta_equiv.Trans)
    qed
  qed
  show ?thesis
    using eqv refl C by (rule aux)
qed

lemma beta_eta_equiv_Imp_left:
  assumes eqv: "beta_eta_equiv \<Gamma> Prop A B"
    and C: "\<Gamma> \<turnstile> C : Prop"
  shows "beta_eta_equiv \<Gamma> Prop (Imp A C) (Imp B C)"
proof -
  have aux: "\<And>\<Delta> \<tau> A B C.
    beta_eta_equiv \<Delta> \<tau> A B \<Longrightarrow> \<tau> = Prop \<Longrightarrow> \<Delta> \<turnstile> C : Prop \<Longrightarrow>
      beta_eta_equiv \<Delta> Prop (Imp A C) (Imp B C)"
  proof -
    fix \<Delta> \<tau> A B C
    assume e: "beta_eta_equiv \<Delta> \<tau> A B"
      and tau: "\<tau> = Prop"
      and C_type: "\<Delta> \<turnstile> C : Prop"
    show "beta_eta_equiv \<Delta> Prop (Imp A C) (Imp B C)"
      using e tau C_type
    proof (induction arbitrary: C)
      case (Refl \<Delta> M \<tau>)
      have M_type: "\<Delta> \<turnstile> M : Prop"
        using Refl.hyps Refl.prems(1) by simp
      show ?case
        using M_type Refl.prems(2) by (intro beta_eta_equiv.Refl has_type.Imp)
    next
      case (Beta \<Delta> M \<tau> N)
      have M_type: "\<Delta> \<turnstile> M : Prop"
        using Beta.hyps(1) Beta.prems(1) by simp
      have N_type: "\<Delta> \<turnstile> N : Prop"
        using Beta.hyps(2) Beta.prems(1) by simp
      have step: "compatible_step beta_contract (Imp M C) (Imp N C)"
        using Beta.hyps(3) by (rule compatible_step.Imp_left)
      show ?case
        using M_type N_type Beta.prems(2) step
        by (intro beta_eta_equiv.Beta has_type.Imp)
    next
      case (Eta \<Delta> M \<tau> N)
      have M_type: "\<Delta> \<turnstile> M : Prop"
        using Eta.hyps(1) Eta.prems(1) by simp
      have N_type: "\<Delta> \<turnstile> N : Prop"
        using Eta.hyps(2) Eta.prems(1) by simp
      have step: "compatible_step eta_contract (Imp M C) (Imp N C)"
        using Eta.hyps(3) by (rule compatible_step.Imp_left)
      show ?case
        using M_type N_type Eta.prems(2) step
        by (intro beta_eta_equiv.Eta has_type.Imp)
    next
      case (Sym \<Delta> \<tau> M N)
      have NM: "beta_eta_equiv \<Delta> Prop (Imp N C) (Imp M C)"
        using Sym.IH Sym.prems by blast
      show ?case
        using NM .
    next
      case (Trans \<Delta> \<tau> M N P)
      have MN: "beta_eta_equiv \<Delta> Prop (Imp M C) (Imp N C)"
        using Trans.IH(1) Trans.prems by blast
      have NP: "beta_eta_equiv \<Delta> Prop (Imp N C) (Imp P C)"
        using Trans.IH(2) Trans.prems by blast
      show ?case
        using MN NP by (rule beta_eta_equiv.Trans)
    qed
  qed
  show ?thesis
    using eqv refl C by (rule aux)
qed

lemma beta_eta_equiv_Imp_right:
  assumes C: "\<Gamma> \<turnstile> C : Prop"
    and eqv: "beta_eta_equiv \<Gamma> Prop A B"
  shows "beta_eta_equiv \<Gamma> Prop (Imp C A) (Imp C B)"
proof -
  have aux: "\<And>\<Delta> \<tau> A B C.
    beta_eta_equiv \<Delta> \<tau> A B \<Longrightarrow> \<tau> = Prop \<Longrightarrow> \<Delta> \<turnstile> C : Prop \<Longrightarrow>
      beta_eta_equiv \<Delta> Prop (Imp C A) (Imp C B)"
  proof -
    fix \<Delta> \<tau> A B C
    assume e: "beta_eta_equiv \<Delta> \<tau> A B"
      and tau: "\<tau> = Prop"
      and C_type: "\<Delta> \<turnstile> C : Prop"
    show "beta_eta_equiv \<Delta> Prop (Imp C A) (Imp C B)"
      using e tau C_type
    proof (induction arbitrary: C)
      case (Refl \<Delta> M \<tau>)
      have M_type: "\<Delta> \<turnstile> M : Prop"
        using Refl.hyps Refl.prems(1) by simp
      show ?case
        using Refl.prems(2) M_type by (intro beta_eta_equiv.Refl has_type.Imp)
    next
      case (Beta \<Delta> M \<tau> N)
      have M_type: "\<Delta> \<turnstile> M : Prop"
        using Beta.hyps(1) Beta.prems(1) by simp
      have N_type: "\<Delta> \<turnstile> N : Prop"
        using Beta.hyps(2) Beta.prems(1) by simp
      have step: "compatible_step beta_contract (Imp C M) (Imp C N)"
        using Beta.hyps(3) by (rule compatible_step.Imp_right)
      show ?case
        using Beta.prems(2) M_type N_type step
        by (intro beta_eta_equiv.Beta has_type.Imp)
    next
      case (Eta \<Delta> M \<tau> N)
      have M_type: "\<Delta> \<turnstile> M : Prop"
        using Eta.hyps(1) Eta.prems(1) by simp
      have N_type: "\<Delta> \<turnstile> N : Prop"
        using Eta.hyps(2) Eta.prems(1) by simp
      have step: "compatible_step eta_contract (Imp C M) (Imp C N)"
        using Eta.hyps(3) by (rule compatible_step.Imp_right)
      show ?case
        using Eta.prems(2) M_type N_type step
        by (intro beta_eta_equiv.Eta has_type.Imp)
    next
      case (Sym \<Delta> \<tau> M N)
      have NM: "beta_eta_equiv \<Delta> Prop (Imp C N) (Imp C M)"
        using Sym.IH Sym.prems by blast
      show ?case
        using NM .
    next
      case (Trans \<Delta> \<tau> M N P)
      have MN: "beta_eta_equiv \<Delta> Prop (Imp C M) (Imp C N)"
        using Trans.IH(1) Trans.prems by blast
      have NP: "beta_eta_equiv \<Delta> Prop (Imp C N) (Imp C P)"
        using Trans.IH(2) Trans.prems by blast
      show ?case
        using MN NP by (rule beta_eta_equiv.Trans)
    qed
  qed
  show ?thesis
    using eqv refl C by (rule aux)
qed

lemma beta_eta_equiv_Forall_body:
  assumes eqv: "beta_eta_equiv (\<sigma> # \<Gamma>) Prop A B"
  shows "beta_eta_equiv \<Gamma> Prop (Forall \<sigma> A) (Forall \<sigma> B)"
proof -
  have aux: "\<And>\<Delta> \<tau> A B \<sigma> \<Gamma>.
    \<Delta> = \<sigma> # \<Gamma> \<Longrightarrow> beta_eta_equiv \<Delta> \<tau> A B \<Longrightarrow> \<tau> = Prop \<Longrightarrow>
      beta_eta_equiv \<Gamma> Prop (Forall \<sigma> A) (Forall \<sigma> B)"
  proof -
    fix \<Delta> \<tau> A B \<sigma> \<Gamma>
    assume delta: "\<Delta> = \<sigma> # \<Gamma>"
      and e: "beta_eta_equiv \<Delta> \<tau> A B"
      and tau: "\<tau> = Prop"
    show "beta_eta_equiv \<Gamma> Prop (Forall \<sigma> A) (Forall \<sigma> B)"
      using e delta tau
    proof (induction arbitrary: \<sigma> \<Gamma>)
      case (Refl \<Delta> M \<tau>)
      have M_type: "\<sigma> # \<Gamma> \<turnstile> M : Prop"
        using Refl.hyps Refl.prems by simp
      show ?case
        using M_type by (intro beta_eta_equiv.Refl has_type.Forall)
    next
      case (Beta \<Delta> M \<tau> N)
      have M_type: "\<sigma> # \<Gamma> \<turnstile> M : Prop"
        using Beta.hyps(1) Beta.prems by simp
      have N_type: "\<sigma> # \<Gamma> \<turnstile> N : Prop"
        using Beta.hyps(2) Beta.prems by simp
      have step: "compatible_step beta_contract (Forall \<sigma> M) (Forall \<sigma> N)"
        using Beta.hyps(3) by (rule compatible_step.Forall_body)
      show ?case
        using M_type N_type step by (intro beta_eta_equiv.Beta has_type.Forall)
    next
      case (Eta \<Delta> M \<tau> N)
      have M_type: "\<sigma> # \<Gamma> \<turnstile> M : Prop"
        using Eta.hyps(1) Eta.prems by simp
      have N_type: "\<sigma> # \<Gamma> \<turnstile> N : Prop"
        using Eta.hyps(2) Eta.prems by simp
      have step: "compatible_step eta_contract (Forall \<sigma> M) (Forall \<sigma> N)"
        using Eta.hyps(3) by (rule compatible_step.Forall_body)
      show ?case
        using M_type N_type step by (intro beta_eta_equiv.Eta has_type.Forall)
    next
      case (Sym \<Delta> \<tau> M N)
      have NM: "beta_eta_equiv \<Gamma> Prop (Forall \<sigma> N) (Forall \<sigma> M)"
        using Sym.IH Sym.prems by blast
      show ?case
        using NM .
    next
      case (Trans \<Delta> \<tau> M N P)
      have MN: "beta_eta_equiv \<Gamma> Prop (Forall \<sigma> M) (Forall \<sigma> N)"
        using Trans.IH(1) Trans.prems by blast
      have NP: "beta_eta_equiv \<Gamma> Prop (Forall \<sigma> N) (Forall \<sigma> P)"
        using Trans.IH(2) Trans.prems by blast
      show ?case
        using MN NP by (rule beta_eta_equiv.Trans)
    qed
  qed
  show ?thesis
    using refl eqv refl by (rule aux)
qed

lemma beta_eta_equiv_Exists_body:
  assumes eqv: "beta_eta_equiv (\<sigma> # \<Gamma>) Prop A B"
  shows "beta_eta_equiv \<Gamma> Prop (Exists \<sigma> A) (Exists \<sigma> B)"
proof -
  have aux: "\<And>\<Delta> \<tau> A B \<sigma> \<Gamma>.
    \<Delta> = \<sigma> # \<Gamma> \<Longrightarrow> beta_eta_equiv \<Delta> \<tau> A B \<Longrightarrow> \<tau> = Prop \<Longrightarrow>
      beta_eta_equiv \<Gamma> Prop (Exists \<sigma> A) (Exists \<sigma> B)"
  proof -
    fix \<Delta> \<tau> A B \<sigma> \<Gamma>
    assume delta: "\<Delta> = \<sigma> # \<Gamma>"
      and e: "beta_eta_equiv \<Delta> \<tau> A B"
      and tau: "\<tau> = Prop"
    show "beta_eta_equiv \<Gamma> Prop (Exists \<sigma> A) (Exists \<sigma> B)"
      using e delta tau
    proof (induction arbitrary: \<sigma> \<Gamma>)
      case (Refl \<Delta> M \<tau>)
      have M_type: "\<sigma> # \<Gamma> \<turnstile> M : Prop"
        using Refl.hyps Refl.prems by simp
      show ?case
        using M_type by (intro beta_eta_equiv.Refl has_type.Exists)
    next
      case (Beta \<Delta> M \<tau> N)
      have M_type: "\<sigma> # \<Gamma> \<turnstile> M : Prop"
        using Beta.hyps(1) Beta.prems by simp
      have N_type: "\<sigma> # \<Gamma> \<turnstile> N : Prop"
        using Beta.hyps(2) Beta.prems by simp
      have step: "compatible_step beta_contract (Exists \<sigma> M) (Exists \<sigma> N)"
        using Beta.hyps(3) by (rule compatible_step.Exists_body)
      show ?case
        using M_type N_type step by (intro beta_eta_equiv.Beta has_type.Exists)
    next
      case (Eta \<Delta> M \<tau> N)
      have M_type: "\<sigma> # \<Gamma> \<turnstile> M : Prop"
        using Eta.hyps(1) Eta.prems by simp
      have N_type: "\<sigma> # \<Gamma> \<turnstile> N : Prop"
        using Eta.hyps(2) Eta.prems by simp
      have step: "compatible_step eta_contract (Exists \<sigma> M) (Exists \<sigma> N)"
        using Eta.hyps(3) by (rule compatible_step.Exists_body)
      show ?case
        using M_type N_type step by (intro beta_eta_equiv.Eta has_type.Exists)
    next
      case (Sym \<Delta> \<tau> M N)
      have NM: "beta_eta_equiv \<Gamma> Prop (Exists \<sigma> N) (Exists \<sigma> M)"
        using Sym.IH Sym.prems by blast
      show ?case
        using NM .
    next
      case (Trans \<Delta> \<tau> M N P)
      have MN: "beta_eta_equiv \<Gamma> Prop (Exists \<sigma> M) (Exists \<sigma> N)"
        using Trans.IH(1) Trans.prems by blast
      have NP: "beta_eta_equiv \<Gamma> Prop (Exists \<sigma> N) (Exists \<sigma> P)"
        using Trans.IH(2) Trans.prems by blast
      show ?case
        using MN NP by (rule beta_eta_equiv.Trans)
    qed
  qed
  show ?thesis
    using refl eqv refl by (rule aux)
qed

lemma beta_eta_equiv_Bicond_left:
  assumes eqv: "beta_eta_equiv \<Gamma> Prop A B"
    and C_type: "\<Gamma> \<turnstile> C : Prop"
  shows "beta_eta_equiv \<Gamma> Prop (A \<longleftrightarrow>\<^sub>o C) (B \<longleftrightarrow>\<^sub>o C)"
proof -
  have A_type: "\<Gamma> \<turnstile> A : Prop"
    using eqv by (rule beta_eta_equiv_left_type)
  have B_type: "\<Gamma> \<turnstile> B : Prop"
    using eqv by (rule beta_eta_equiv_right_type)
  have AC_type: "\<Gamma> \<turnstile> Imp A C : Prop"
    using A_type C_type by auto
  have BC_type: "\<Gamma> \<turnstile> Imp B C : Prop"
    using B_type C_type by auto
  have CA_type: "\<Gamma> \<turnstile> Imp C A : Prop"
    using C_type A_type by auto
  have left_eqv: "beta_eta_equiv \<Gamma> Prop (Imp A C) (Imp B C)"
    using eqv C_type by (rule beta_eta_equiv_Imp_left)
  have right_eqv: "beta_eta_equiv \<Gamma> Prop (Imp C A) (Imp C B)"
    using C_type eqv by (rule beta_eta_equiv_Imp_right)
  have step1: "beta_eta_equiv \<Gamma> Prop
      (Conj (Imp A C) (Imp C A))
      (Conj (Imp B C) (Imp C A))"
    using left_eqv CA_type by (rule beta_eta_equiv_Conj_left)
  have step2: "beta_eta_equiv \<Gamma> Prop
      (Conj (Imp B C) (Imp C A))
      (Conj (Imp B C) (Imp C B))"
    using BC_type right_eqv by (rule beta_eta_equiv_Conj_right)
  show ?thesis
    using step1 step2 by (rule beta_eta_equiv.Trans)
qed

lemma beta_eta_equiv_Bicond_right:
  assumes C_type: "\<Gamma> \<turnstile> C : Prop"
    and eqv: "beta_eta_equiv \<Gamma> Prop A B"
  shows "beta_eta_equiv \<Gamma> Prop (C \<longleftrightarrow>\<^sub>o A) (C \<longleftrightarrow>\<^sub>o B)"
proof -
  have A_type: "\<Gamma> \<turnstile> A : Prop"
    using eqv by (rule beta_eta_equiv_left_type)
  have B_type: "\<Gamma> \<turnstile> B : Prop"
    using eqv by (rule beta_eta_equiv_right_type)
  have CB_type: "\<Gamma> \<turnstile> Imp C B : Prop"
    using C_type B_type by auto
  have AC_type: "\<Gamma> \<turnstile> Imp A C : Prop"
    using A_type C_type by auto
  have left_eqv: "beta_eta_equiv \<Gamma> Prop (Imp C A) (Imp C B)"
    using C_type eqv by (rule beta_eta_equiv_Imp_right)
  have right_eqv: "beta_eta_equiv \<Gamma> Prop (Imp A C) (Imp B C)"
    using eqv C_type by (rule beta_eta_equiv_Imp_left)
  have step1: "beta_eta_equiv \<Gamma> Prop
      (Conj (Imp C A) (Imp A C))
      (Conj (Imp C B) (Imp A C))"
    using left_eqv AC_type by (rule beta_eta_equiv_Conj_left)
  have step2: "beta_eta_equiv \<Gamma> Prop
      (Conj (Imp C B) (Imp A C))
      (Conj (Imp C B) (Imp B C))"
    using CB_type right_eqv by (rule beta_eta_equiv_Conj_right)
  show ?thesis
    using step1 step2 by (rule beta_eta_equiv.Trans)
qed

lemma beta_eta_caie_heq_apply:
  assumes x: "\<Gamma> \<turnstile> x : Ind"
    and y: "\<Gamma> \<turnstile> y : Ind"
  shows "beta_eta_equiv \<Gamma> Prop (App (caie_heq x) y) (Eq Ind y x)"
proof -
  have left_type: "\<Gamma> \<turnstile> App (caie_heq x) y : Prop"
    using typed_caie_heq[OF x] y
    by (auto simp: caie_prop_ty_def pred_ty_def)
  have right_type: "\<Gamma> \<turnstile> Eq Ind y x : Prop"
    using x y by auto
  have step: "compatible_step beta_contract (App (caie_heq x) y) (Eq Ind y x)"
  proof -
    have "compatible_step beta_contract (App (caie_heq x) y)
        (subst0 y (Eq Ind (Var 0) (shift x)))"
      unfolding caie_heq_def by (intro compatible_step.root beta_contract.beta)
    then show ?thesis
      by (simp add: subst0_def)
  qed
  show ?thesis
    using left_type right_type step by (rule beta_eta_equiv.Beta)
qed

lemma H_caie_heq_apply:
  assumes "\<Gamma> \<turnstile> x : Ind"
    and "\<Gamma> \<turnstile> y : Ind"
  shows "\<Gamma> \<turnstile>\<^sub>H (App (caie_heq x) y \<longleftrightarrow>\<^sub>o Eq Ind y x)"
  using beta_eta_caie_heq_apply[OF assms] by (rule H_beta_eta_equiv)

lemma CEV_caie_heq_apply:
  assumes "\<Gamma> \<turnstile> x : Ind"
    and "\<Gamma> \<turnstile> y : Ind"
  shows "\<Gamma> \<turnstile>\<^sub>CEV (App (caie_heq x) y \<longleftrightarrow>\<^sub>o Eq Ind y x)"
  using beta_eta_caie_heq_apply[OF assms] by (rule CEV_beta_eta_equiv)

lemma beta_eta_caie_down_apply:
  assumes Q: "\<Gamma> \<turnstile> Q : caie_classifier_ty"
    and x: "\<Gamma> \<turnstile> x : Ind"
  shows "beta_eta_equiv \<Gamma> Prop (App (Q\<^sup>\<down>\<^sub>c) x) (App Q (caie_heq x))"
proof -
  let ?D = "Lam Ind (App (shift Q) (caie_heq (Var 0)))"
  have down_type: "\<Gamma> \<turnstile> Q\<^sup>\<down>\<^sub>c : caie_prop_ty"
    using Q by (rule typed_caie_down)
  have left_type: "\<Gamma> \<turnstile> App (Q\<^sup>\<down>\<^sub>c) x : Prop"
    using down_type x by (auto simp: caie_prop_ty_def pred_ty_def)
  have shifted_Q: "Ind # \<Gamma> \<turnstile> shift Q : caie_classifier_ty"
    using Q by (rule weakening_front)
  have var0_type: "Ind # \<Gamma> \<turnstile> Var 0 : Ind"
    by auto
  have heq_var_type: "Ind # \<Gamma> \<turnstile> caie_heq (Var 0) : caie_prop_ty"
    using var0_type by (rule typed_caie_heq)
  have D_body_type: "Ind # \<Gamma> \<turnstile> App (shift Q) (caie_heq (Var 0)) : Prop"
    using shifted_Q heq_var_type by (auto simp: caie_classifier_ty_def)
  have D_type: "\<Gamma> \<turnstile> ?D : caie_prop_ty"
    using D_body_type by (auto simp: caie_prop_ty_def pred_ty_def)
  have mid_type: "\<Gamma> \<turnstile> App ?D x : Prop"
    using D_type x by (auto simp: caie_prop_ty_def pred_ty_def)
  have heq_x_type: "\<Gamma> \<turnstile> caie_heq x : caie_prop_ty"
    using x by (rule typed_caie_heq)
  have right_type: "\<Gamma> \<turnstile> App Q (caie_heq x) : Prop"
    using Q heq_x_type by (auto simp: caie_classifier_ty_def)

  have step_down: "compatible_step beta_contract (Q\<^sup>\<down>\<^sub>c) ?D"
  proof -
    have "compatible_step beta_contract (App caie_down_op Q)
        (subst0 Q (Lam Ind (App (Var 1) (caie_heq (Var 0)))))"
      unfolding caie_down_op_def
      by (intro compatible_step.root beta_contract.beta)
    then show ?thesis
      by (simp add: subst0_def shift_def)
  qed
  have step1: "compatible_step beta_contract (App (Q\<^sup>\<down>\<^sub>c) x) (App ?D x)"
    using step_down by (rule compatible_step.App_left)
  have eqv1: "beta_eta_equiv \<Gamma> Prop (App (Q\<^sup>\<down>\<^sub>c) x) (App ?D x)"
    using left_type mid_type step1 by (rule beta_eta_equiv.Beta)

  have step2: "compatible_step beta_contract (App ?D x) (App Q (caie_heq x))"
  proof -
    have "compatible_step beta_contract (App ?D x)
        (subst0 x (App (shift Q) (caie_heq (Var 0))))"
      by (intro compatible_step.root beta_contract.beta)
    then show ?thesis
      by (simp add: subst0_def)
  qed
  have eqv2: "beta_eta_equiv \<Gamma> Prop (App ?D x) (App Q (caie_heq x))"
    using mid_type right_type step2 by (rule beta_eta_equiv.Beta)
  show ?thesis
    by (rule beta_eta_equiv.Trans[OF eqv1 eqv2])
qed

lemma H_caie_down_apply:
  assumes "\<Gamma> \<turnstile> Q : caie_classifier_ty"
    and "\<Gamma> \<turnstile> x : Ind"
  shows "\<Gamma> \<turnstile>\<^sub>H (App (Q\<^sup>\<down>\<^sub>c) x \<longleftrightarrow>\<^sub>o App Q (caie_heq x))"
  using beta_eta_caie_down_apply[OF assms] by (rule H_beta_eta_equiv)

lemma CEV_caie_down_apply:
  assumes "\<Gamma> \<turnstile> Q : caie_classifier_ty"
    and "\<Gamma> \<turnstile> x : Ind"
  shows "\<Gamma> \<turnstile>\<^sub>CEV (App (Q\<^sup>\<down>\<^sub>c) x \<longleftrightarrow>\<^sub>o App Q (caie_heq x))"
  using beta_eta_caie_down_apply[OF assms] by (rule CEV_beta_eta_equiv)

lemma beta_eta_caie_up_apply:
  assumes P: "\<Gamma> \<turnstile> P : caie_prop_ty"
    and R: "\<Gamma> \<turnstile> R : caie_prop_ty"
  shows "beta_eta_equiv \<Gamma> Prop (App (P\<^sup>\<up>\<^sub>c) R) (caie_up_body P R)"
proof -
  let ?U = "Lam caie_prop_ty (caie_up_body (shift P) (Var 0))"
  have up_type: "\<Gamma> \<turnstile> P\<^sup>\<up>\<^sub>c : caie_classifier_ty"
    using P by (rule typed_caie_up)
  have left_type: "\<Gamma> \<turnstile> App (P\<^sup>\<up>\<^sub>c) R : Prop"
    using up_type R by (auto simp: caie_classifier_ty_def)
  have shifted_P: "caie_prop_ty # \<Gamma> \<turnstile> shift P : caie_prop_ty"
    using P by (rule weakening_front)
  have var0_type: "caie_prop_ty # \<Gamma> \<turnstile> Var 0 : caie_prop_ty"
    by auto
  have U_body_type: "caie_prop_ty # \<Gamma> \<turnstile> caie_up_body (shift P) (Var 0) : Prop"
    using shifted_P var0_type by (rule typed_caie_up_body)
  have U_type: "\<Gamma> \<turnstile> ?U : caie_classifier_ty"
    using U_body_type by (auto simp: caie_classifier_ty_def)
  have mid_type: "\<Gamma> \<turnstile> App ?U R : Prop"
    using U_type R by (auto simp: caie_classifier_ty_def)
  have right_type: "\<Gamma> \<turnstile> caie_up_body P R : Prop"
    using P R by (rule typed_caie_up_body)

  have step_up: "compatible_step beta_contract (P\<^sup>\<up>\<^sub>c) ?U"
  proof -
      have "compatible_step beta_contract (App caie_up_op P)
          (subst0 P (Lam caie_prop_ty (caie_up_body (Var 1) (Var 0))))"
        unfolding caie_up_op_as_body by (intro compatible_step.root beta_contract.beta)
      then show ?thesis
        by (simp add: subst0_def subst_lift_caie_up_body_Var1_Var0)
    qed
  have step1: "compatible_step beta_contract (App (P\<^sup>\<up>\<^sub>c) R) (App ?U R)"
    using step_up by (rule compatible_step.App_left)
  have eqv1: "beta_eta_equiv \<Gamma> Prop (App (P\<^sup>\<up>\<^sub>c) R) (App ?U R)"
    using left_type mid_type step1 by (rule beta_eta_equiv.Beta)

  have step2: "compatible_step beta_contract (App ?U R) (caie_up_body P R)"
    proof -
      have "compatible_step beta_contract (App ?U R)
          (subst0 R (caie_up_body (shift P) (Var 0)))"
        by (intro compatible_step.root beta_contract.beta)
      then show ?thesis
        by (simp add: subst0_caie_up_body_shift_Var0)
    qed
  have eqv2: "beta_eta_equiv \<Gamma> Prop (App ?U R) (caie_up_body P R)"
    using mid_type right_type step2 by (rule beta_eta_equiv.Beta)
  show ?thesis
    by (rule beta_eta_equiv.Trans[OF eqv1 eqv2])
qed

lemma H_caie_up_apply:
  assumes "\<Gamma> \<turnstile> P : caie_prop_ty"
    and "\<Gamma> \<turnstile> R : caie_prop_ty"
  shows "\<Gamma> \<turnstile>\<^sub>H (App (P\<^sup>\<up>\<^sub>c) R \<longleftrightarrow>\<^sub>o caie_up_body P R)"
  using beta_eta_caie_up_apply[OF assms] by (rule H_beta_eta_equiv)

lemma CEV_caie_up_apply:
  assumes "\<Gamma> \<turnstile> P : caie_prop_ty"
    and "\<Gamma> \<turnstile> R : caie_prop_ty"
  shows "\<Gamma> \<turnstile>\<^sub>CEV (App (P\<^sup>\<up>\<^sub>c) R \<longleftrightarrow>\<^sub>o caie_up_body P R)"
  using beta_eta_caie_up_apply[OF assms] by (rule CEV_beta_eta_equiv)

lemma beta_eta_caie_dsim:
  assumes Q: "\<Gamma> \<turnstile> Q : caie_classifier_ty"
    and Z: "\<Gamma> \<turnstile> Z : caie_classifier_ty"
  shows "beta_eta_equiv \<Gamma> Prop (Q \<sim>\<^sub>\<down>c Z)
    (Eq caie_prop_ty (Q\<^sup>\<down>\<^sub>c) (Z\<^sup>\<down>\<^sub>c))"
proof -
  let ?F = "Lam caie_classifier_ty
    (Eq caie_prop_ty ((shift Q)\<^sup>\<down>\<^sub>c) ((Var 0)\<^sup>\<down>\<^sub>c))"
  have left_type: "\<Gamma> \<turnstile> Q \<sim>\<^sub>\<down>c Z : Prop"
    using Q Z by (rule typed_caie_dsim)
  have shifted_Q: "caie_classifier_ty # \<Gamma> \<turnstile> shift Q : caie_classifier_ty"
    using Q by (rule weakening_front)
  have var0_type: "caie_classifier_ty # \<Gamma> \<turnstile> Var 0 : caie_classifier_ty"
    by auto
  have down_shifted_Q:
      "caie_classifier_ty # \<Gamma> \<turnstile> (shift Q)\<^sup>\<down>\<^sub>c : caie_prop_ty"
    using shifted_Q by (rule typed_caie_down)
  have down_var0: "caie_classifier_ty # \<Gamma> \<turnstile> (Var 0)\<^sup>\<down>\<^sub>c : caie_prop_ty"
    using var0_type by (rule typed_caie_down)
  have F_body_type: "caie_classifier_ty # \<Gamma> \<turnstile>
      Eq caie_prop_ty ((shift Q)\<^sup>\<down>\<^sub>c) ((Var 0)\<^sup>\<down>\<^sub>c) : Prop"
    using down_shifted_Q down_var0 by auto
  have F_type: "\<Gamma> \<turnstile> ?F : caie_classifier_ty \<rightarrow>\<^sub>o Prop"
    using F_body_type by auto
  have mid_type: "\<Gamma> \<turnstile> App ?F Z : Prop"
    using F_type Z by auto
  have Q_down_type: "\<Gamma> \<turnstile> Q\<^sup>\<down>\<^sub>c : caie_prop_ty"
    using Q by (rule typed_caie_down)
  have Z_down_type: "\<Gamma> \<turnstile> Z\<^sup>\<down>\<^sub>c : caie_prop_ty"
    using Z by (rule typed_caie_down)
  have right_type: "\<Gamma> \<turnstile> Eq caie_prop_ty (Q\<^sup>\<down>\<^sub>c) (Z\<^sup>\<down>\<^sub>c) : Prop"
    using Q_down_type Z_down_type by auto

  have step_dsim: "compatible_step beta_contract (App caie_dsim_op Q) ?F"
  proof -
      have "compatible_step beta_contract (App caie_dsim_op Q)
          (subst0 Q
            (Lam caie_classifier_ty
              (Eq caie_prop_ty ((Var 1)\<^sup>\<down>\<^sub>c) ((Var 0)\<^sup>\<down>\<^sub>c))))"
        unfolding caie_dsim_op_def
        by (intro compatible_step.root beta_contract.beta)
      then show ?thesis
        by (simp add: subst0_def subst_lift_caie_dsim_body_Var1_Var0 shift_def)
    qed
  have step1: "compatible_step beta_contract (Q \<sim>\<^sub>\<down>c Z) (App ?F Z)"
    using step_dsim by (rule compatible_step.App_left)
  have eqv1: "beta_eta_equiv \<Gamma> Prop (Q \<sim>\<^sub>\<down>c Z) (App ?F Z)"
    using left_type mid_type step1 by (rule beta_eta_equiv.Beta)

  have step2: "compatible_step beta_contract (App ?F Z)
      (Eq caie_prop_ty (Q\<^sup>\<down>\<^sub>c) (Z\<^sup>\<down>\<^sub>c))"
  proof -
      have "compatible_step beta_contract (App ?F Z)
          (subst0 Z (Eq caie_prop_ty ((shift Q)\<^sup>\<down>\<^sub>c) ((Var 0)\<^sup>\<down>\<^sub>c)))"
        by (intro compatible_step.root beta_contract.beta)
      then show ?thesis
        by (simp add: subst0_caie_dsim_body_shift_Var0)
    qed
  have eqv2: "beta_eta_equiv \<Gamma> Prop (App ?F Z)
      (Eq caie_prop_ty (Q\<^sup>\<down>\<^sub>c) (Z\<^sup>\<down>\<^sub>c))"
    using mid_type right_type step2 by (rule beta_eta_equiv.Beta)
  show ?thesis
    by (rule beta_eta_equiv.Trans[OF eqv1 eqv2])
qed

lemma H_caie_dsim:
  assumes "\<Gamma> \<turnstile> Q : caie_classifier_ty"
    and "\<Gamma> \<turnstile> Z : caie_classifier_ty"
  shows "\<Gamma> \<turnstile>\<^sub>H
    (Q \<sim>\<^sub>\<down>c Z \<longleftrightarrow>\<^sub>o Eq caie_prop_ty (Q\<^sup>\<down>\<^sub>c) (Z\<^sup>\<down>\<^sub>c))"
  using beta_eta_caie_dsim[OF assms] by (rule H_beta_eta_equiv)

lemma CEV_caie_dsim:
  assumes "\<Gamma> \<turnstile> Q : caie_classifier_ty"
    and "\<Gamma> \<turnstile> Z : caie_classifier_ty"
  shows "\<Gamma> \<turnstile>\<^sub>CEV
    (Q \<sim>\<^sub>\<down>c Z \<longleftrightarrow>\<^sub>o Eq caie_prop_ty (Q\<^sup>\<down>\<^sub>c) (Z\<^sup>\<down>\<^sub>c))"
  using beta_eta_caie_dsim[OF assms] by (rule CEV_beta_eta_equiv)


subsection \<open>Local Caie derivability from explicit assumptions\<close>

text \<open>
  The Caie development keeps the extra name/counterfactual principles explicit.
  The following lightweight wrapper lets us reason from a finite list of
  Caie-specific assumptions while still importing all global @{term CEV} theorems.
\<close>

inductive caie_CEV_derivable :: "ctx \<Rightarrow> oterm list \<Rightarrow> oterm \<Rightarrow> bool" where
  caie_Assumption[intro]:
    "A \<in> set \<Delta> \<Longrightarrow> \<Gamma> \<turnstile> A : Prop \<Longrightarrow> caie_CEV_derivable \<Gamma> \<Delta> A"
| caie_Theorem[intro]:
    "\<Gamma> \<turnstile>\<^sub>CEV A \<Longrightarrow> caie_CEV_derivable \<Gamma> \<Delta> A"
| caie_MP[intro]:
    "caie_CEV_derivable \<Gamma> \<Delta> A \<Longrightarrow>
     caie_CEV_derivable \<Gamma> \<Delta> (Imp A B) \<Longrightarrow>
     caie_CEV_derivable \<Gamma> \<Delta> B"

lemma caie_CEV_derivable_formula:
  assumes "caie_CEV_derivable \<Gamma> \<Delta> A"
  shows "\<Gamma> \<turnstile> A : Prop"
  using assms
proof (induction rule: caie_CEV_derivable.induct)
  case (caie_Assumption A \<Delta> \<Gamma>)
  then show ?case by simp
next
  case (caie_Theorem \<Gamma> A \<Delta>)
  then show ?case by (rule CEV_proves_formula)
next
  case (caie_MP \<Gamma> \<Delta> A B)
  then show ?case by (auto elim: has_type.cases)
qed

lemma caie_CEV_derivable_mono:
  assumes "caie_CEV_derivable \<Gamma> \<Delta> A"
    and "set \<Delta> \<subseteq> set \<Delta>'"
  shows "caie_CEV_derivable \<Gamma> \<Delta>' A"
  using assms
proof (induction arbitrary: \<Delta>' rule: caie_CEV_derivable.induct)
  case (caie_Assumption A \<Delta> \<Gamma>)
  then show ?case by auto
next
  case (caie_Theorem \<Gamma> A \<Delta>)
  then show ?case by auto
next
  case (caie_MP \<Gamma> \<Delta> A B)
  then show ?case by auto
qed

lemma caie_CEV_derivable_of_theorem:
  assumes "\<Gamma> \<turnstile>\<^sub>CEV A"
  shows "caie_CEV_derivable \<Gamma> \<Delta> A"
  using assms by (rule caie_CEV_derivable.caie_Theorem)

lemma CEV_from_of_caie_CEV_derivable_singleton:
  assumes "caie_CEV_derivable \<Gamma> \<Delta> B"
    and "\<Delta> = [A]"
  shows "CEV_from \<Gamma> A B"
  using assms
proof (induction arbitrary: A rule: caie_CEV_derivable.induct)
  case (caie_Assumption B \<Delta> \<Gamma>)
  then show ?case by auto
next
  case (caie_Theorem \<Gamma> B \<Delta>)
  then show ?case by auto
next
  case (caie_MP \<Gamma> \<Delta> B C)
  then show ?case by auto
qed

lemma caie_CEV_derivable_singleton_deduction:
  assumes "caie_CEV_derivable \<Gamma> [A] B"
    and "\<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>CEV Imp A B"
  using CEV_from_of_caie_CEV_derivable_singleton[OF assms(1) refl] assms(2)
  by (rule CEV_from_deduction)

lemma caie_CEV_derivable_conj_intro:
  assumes "caie_CEV_derivable \<Gamma> \<Delta> A"
    and "caie_CEV_derivable \<Gamma> \<Delta> B"
  shows "caie_CEV_derivable \<Gamma> \<Delta> (Conj A B)"
proof -
  have A_type: "\<Gamma> \<turnstile> A : Prop"
    using assms(1) by (rule caie_CEV_derivable_formula)
  have B_type: "\<Gamma> \<turnstile> B : Prop"
    using assms(2) by (rule caie_CEV_derivable_formula)
  have taut: "prop_tautology \<Gamma> (Imp A (Imp B (Conj A B)))"
    unfolding prop_tautology_def using A_type B_type by auto
  have d_taut: "caie_CEV_derivable \<Gamma> \<Delta> (Imp A (Imp B (Conj A B)))"
    using CEV_prop_tautology[OF taut] by (rule caie_CEV_derivable_of_theorem)
  have d_imp: "caie_CEV_derivable \<Gamma> \<Delta> (Imp B (Conj A B))"
    using assms(1) d_taut by (rule caie_CEV_derivable.caie_MP)
  show ?thesis
    using assms(2) d_imp by (rule caie_CEV_derivable.caie_MP)
qed

lemma caie_CEV_derivable_bicond_left:
  assumes A_type: "\<Gamma> \<turnstile> A : Prop"
    and B_type: "\<Gamma> \<turnstile> B : Prop"
    and d_bicond: "caie_CEV_derivable \<Gamma> \<Delta> (A \<longleftrightarrow>\<^sub>o B)"
    and d_A: "caie_CEV_derivable \<Gamma> \<Delta> A"
  shows "caie_CEV_derivable \<Gamma> \<Delta> B"
proof -
  have bicond_type: "\<Gamma> \<turnstile> (A \<longleftrightarrow>\<^sub>o B) : Prop"
    using A_type B_type by auto
  have taut: "prop_tautology \<Gamma> (Imp (A \<longleftrightarrow>\<^sub>o B) (Imp A B))"
    unfolding prop_tautology_def
    using A_type B_type bicond_type by auto
  have d_rule: "caie_CEV_derivable \<Gamma> \<Delta>
      (Imp (A \<longleftrightarrow>\<^sub>o B) (Imp A B))"
    using CEV_prop_tautology[OF taut] by (rule caie_CEV_derivable_of_theorem)
  have d_imp: "caie_CEV_derivable \<Gamma> \<Delta> (Imp A B)"
    using d_bicond d_rule by (rule caie_CEV_derivable.caie_MP)
  show ?thesis
    using d_A d_imp by (rule caie_CEV_derivable.caie_MP)
qed

lemma caie_CEV_derivable_bicond_right:
  assumes A_type: "\<Gamma> \<turnstile> A : Prop"
    and B_type: "\<Gamma> \<turnstile> B : Prop"
    and d_bicond: "caie_CEV_derivable \<Gamma> \<Delta> (A \<longleftrightarrow>\<^sub>o B)"
    and d_B: "caie_CEV_derivable \<Gamma> \<Delta> B"
  shows "caie_CEV_derivable \<Gamma> \<Delta> A"
proof -
  have bicond_type: "\<Gamma> \<turnstile> (A \<longleftrightarrow>\<^sub>o B) : Prop"
    using A_type B_type by auto
  have taut: "prop_tautology \<Gamma> (Imp (A \<longleftrightarrow>\<^sub>o B) (Imp B A))"
    unfolding prop_tautology_def
    using A_type B_type bicond_type by auto
  have d_rule: "caie_CEV_derivable \<Gamma> \<Delta>
      (Imp (A \<longleftrightarrow>\<^sub>o B) (Imp B A))"
    using CEV_prop_tautology[OF taut] by (rule caie_CEV_derivable_of_theorem)
  have d_imp: "caie_CEV_derivable \<Gamma> \<Delta> (Imp B A)"
    using d_bicond d_rule by (rule caie_CEV_derivable.caie_MP)
  show ?thesis
    using d_B d_imp by (rule caie_CEV_derivable.caie_MP)
qed

lemma CEV_imp_trans:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile> B : Prop"
    and "\<Gamma> \<turnstile> C : Prop"
    and "\<Gamma> \<turnstile>\<^sub>CEV Imp A B"
    and "\<Gamma> \<turnstile>\<^sub>CEV Imp B C"
  shows "\<Gamma> \<turnstile>\<^sub>CEV Imp A C"
proof -
  have AB_type: "\<Gamma> \<turnstile> Imp A B : Prop"
    using assms(1,2) by auto
  have BC_type: "\<Gamma> \<turnstile> Imp B C : Prop"
    using assms(2,3) by auto
  have taut: "prop_tautology \<Gamma>
      (Imp (Imp A B) (Imp (Imp B C) (Imp A C)))"
    unfolding prop_tautology_def
    using assms(1,2,3) AB_type BC_type by auto
  have "\<Gamma> \<turnstile>\<^sub>CEV Imp (Imp A B) (Imp (Imp B C) (Imp A C))"
    by (rule CEV_prop_tautology[OF taut])
  then have "\<Gamma> \<turnstile>\<^sub>CEV Imp (Imp B C) (Imp A C)"
    by (rule CEV_proves.MP[OF assms(4)])
  then show ?thesis
    by (rule CEV_proves.MP[OF assms(5)])
qed

lemma CEV_imp_lift_right:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile> B : Prop"
    and "\<Gamma> \<turnstile> C : Prop"
    and "\<Gamma> \<turnstile>\<^sub>CEV Imp B C"
  shows "\<Gamma> \<turnstile>\<^sub>CEV Imp (Imp A B) (Imp A C)"
proof -
  have BC_type: "\<Gamma> \<turnstile> Imp B C : Prop"
    using assms(2,3) by auto
  have AB_type: "\<Gamma> \<turnstile> Imp A B : Prop"
    using assms(1,2) by auto
  have AC_type: "\<Gamma> \<turnstile> Imp A C : Prop"
    using assms(1,3) by auto
  have taut: "prop_tautology \<Gamma>
      (Imp (Imp B C) (Imp (Imp A B) (Imp A C)))"
    unfolding prop_tautology_def
    using assms(1,2,3) BC_type AB_type AC_type by auto
  have "\<Gamma> \<turnstile>\<^sub>CEV
      Imp (Imp B C) (Imp (Imp A B) (Imp A C))"
    by (rule CEV_prop_tautology[OF taut])
  then show ?thesis
    by (rule CEV_proves.MP[OF assms(4)])
qed

lemma CEV_bicond_replace_right:
  assumes "\<Gamma> \<turnstile> X : Prop"
    and "\<Gamma> \<turnstile> Y : Prop"
    and "\<Gamma> \<turnstile> Z : Prop"
    and "\<Gamma> \<turnstile>\<^sub>CEV (Y \<longleftrightarrow>\<^sub>o Z)"
  shows "\<Gamma> \<turnstile>\<^sub>CEV Imp (X \<longleftrightarrow>\<^sub>o Z) (X \<longleftrightarrow>\<^sub>o Y)"
proof -
  have XZ_type: "\<Gamma> \<turnstile> (X \<longleftrightarrow>\<^sub>o Z) : Prop"
    using assms(1,3) by auto
  have XY_type: "\<Gamma> \<turnstile> (X \<longleftrightarrow>\<^sub>o Y) : Prop"
    using assms(1,2) by auto
  have ZY_type: "\<Gamma> \<turnstile> (Z \<longleftrightarrow>\<^sub>o Y) : Prop"
    using assms(2,3) by auto
  have sym_taut: "prop_tautology \<Gamma>
      (Imp (Y \<longleftrightarrow>\<^sub>o Z) (Z \<longleftrightarrow>\<^sub>o Y))"
    using assms(2,3) by (rule prop_tautology_bicond_sym)
  have sym_imp: "\<Gamma> \<turnstile>\<^sub>CEV
      Imp (Y \<longleftrightarrow>\<^sub>o Z) (Z \<longleftrightarrow>\<^sub>o Y)"
    by (rule CEV_prop_tautology[OF sym_taut])
  have ZY: "\<Gamma> \<turnstile>\<^sub>CEV (Z \<longleftrightarrow>\<^sub>o Y)"
    using assms(4) sym_imp by (rule CEV_proves.MP)
  have trans_taut: "prop_tautology \<Gamma>
      (Imp (X \<longleftrightarrow>\<^sub>o Z)
        (Imp (Z \<longleftrightarrow>\<^sub>o Y) (X \<longleftrightarrow>\<^sub>o Y)))"
    using assms(1,3,2) by (rule prop_tautology_bicond_trans)
  have trans_imp: "\<Gamma> \<turnstile>\<^sub>CEV
      Imp (X \<longleftrightarrow>\<^sub>o Z)
        (Imp (Z \<longleftrightarrow>\<^sub>o Y) (X \<longleftrightarrow>\<^sub>o Y))"
    by (rule CEV_prop_tautology[OF trans_taut])
  have local: "CEV_from \<Gamma> (X \<longleftrightarrow>\<^sub>o Z) (X \<longleftrightarrow>\<^sub>o Y)"
  proof -
    have local_XZ: "CEV_from \<Gamma> (X \<longleftrightarrow>\<^sub>o Z) (X \<longleftrightarrow>\<^sub>o Z)"
      by (intro CEV_from.Assumption XZ_type)
    have local_tail:
        "CEV_from \<Gamma> (X \<longleftrightarrow>\<^sub>o Z)
          (Imp (Z \<longleftrightarrow>\<^sub>o Y) (X \<longleftrightarrow>\<^sub>o Y))"
      by (rule CEV_from.MP[OF local_XZ CEV_from.Theorem[OF trans_imp]])
    have local_ZY: "CEV_from \<Gamma> (X \<longleftrightarrow>\<^sub>o Z) (Z \<longleftrightarrow>\<^sub>o Y)"
      by (intro CEV_from.Theorem ZY)
    show ?thesis
      by (rule CEV_from.MP[OF local_ZY local_tail])
  qed
  show ?thesis
    using local XZ_type by (rule CEV_from_deduction)
qed

lemma CEV_bicond_replace_left:
  assumes "\<Gamma> \<turnstile> X : Prop"
    and "\<Gamma> \<turnstile> Y : Prop"
    and "\<Gamma> \<turnstile> Z : Prop"
    and "\<Gamma> \<turnstile>\<^sub>CEV (X \<longleftrightarrow>\<^sub>o Y)"
  shows "\<Gamma> \<turnstile>\<^sub>CEV Imp (Y \<longleftrightarrow>\<^sub>o Z) (X \<longleftrightarrow>\<^sub>o Z)"
proof -
  have trans_taut: "prop_tautology \<Gamma>
      (Imp (X \<longleftrightarrow>\<^sub>o Y)
        (Imp (Y \<longleftrightarrow>\<^sub>o Z) (X \<longleftrightarrow>\<^sub>o Z)))"
    using assms(1,2,3) by (rule prop_tautology_bicond_trans)
  have "\<Gamma> \<turnstile>\<^sub>CEV
      Imp (X \<longleftrightarrow>\<^sub>o Y)
        (Imp (Y \<longleftrightarrow>\<^sub>o Z) (X \<longleftrightarrow>\<^sub>o Z))"
    by (rule CEV_prop_tautology[OF trans_taut])
  then show ?thesis
    by (rule CEV_proves.MP[OF assms(4)])
qed

lemma CEV_curry_conj:
  assumes "\<Gamma> \<turnstile> P : Prop"
    and "\<Gamma> \<turnstile> Q : Prop"
    and "\<Gamma> \<turnstile> R : Prop"
    and "\<Gamma> \<turnstile>\<^sub>CEV Imp P (Imp Q R)"
  shows "\<Gamma> \<turnstile>\<^sub>CEV Imp (Conj P Q) R"
proof -
  have imp_type: "\<Gamma> \<turnstile> Imp P (Imp Q R) : Prop"
    using assms(1,2,3) by auto
  have conj_type: "\<Gamma> \<turnstile> Conj P Q : Prop"
    using assms(1,2) by auto
  have taut: "prop_tautology \<Gamma>
      (Imp (Imp P (Imp Q R)) (Imp (Conj P Q) R))"
    unfolding prop_tautology_def
    using assms(1,2,3) imp_type conj_type by auto
  have "\<Gamma> \<turnstile>\<^sub>CEV
      Imp (Imp P (Imp Q R)) (Imp (Conj P Q) R)"
    by (rule CEV_prop_tautology[OF taut])
  then show ?thesis
    by (rule CEV_proves.MP[OF assms(4)])
qed

lemma CEV_uncurry_conj_imp:
  assumes "\<Gamma> \<turnstile> P : Prop"
    and "\<Gamma> \<turnstile> Q : Prop"
    and "\<Gamma> \<turnstile> R : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>CEV
    Imp (Imp (Conj P Q) R) (Imp P (Imp Q R))"
proof -
  have conj_type: "\<Gamma> \<turnstile> Conj P Q : Prop"
    using assms(1,2) by auto
  have left_type: "\<Gamma> \<turnstile> Imp (Conj P Q) R : Prop"
    using conj_type assms(3) by auto
  have right_type: "\<Gamma> \<turnstile> Imp P (Imp Q R) : Prop"
    using assms by auto
  have taut: "prop_tautology \<Gamma>
      (Imp (Imp (Conj P Q) R) (Imp P (Imp Q R)))"
    unfolding prop_tautology_def
    using assms conj_type left_type right_type by auto
  then show ?thesis
    by (rule CEV_prop_tautology)
qed

lemma weakening_after_front:
  assumes "\<sigma> # \<Gamma> \<turnstile> A : \<tau>"
  shows "\<sigma> # \<rho> # \<Gamma> \<turnstile> rename (lift_ren Suc) A : \<tau>"
  using assms
  by (rule renaming_preserves_typing)
    (case_tac n; auto simp: lookup_def nth_Cons split: if_splits)

lemma subst0_Var0_rename_lift_Suc[simp]:
  "subst0 (Var 0) (rename (lift_ren Suc) A) = A"
  unfolding subst0_def
  by (rule subst_rename_inverse) (case_tac n; simp)

lemma CEV_shifted_forall_inst_Var0:
  assumes "\<sigma> # \<Gamma> \<turnstile> A : Prop"
  shows "\<sigma> # \<Gamma> \<turnstile>\<^sub>CEV Imp (shift (Forall \<sigma> A)) A"
proof -
  have body_type_for_ui:
      "\<sigma> # \<sigma> # \<Gamma> \<turnstile> rename (lift_ren Suc) A : Prop"
    using assms by (rule weakening_after_front)
  have var0_type: "\<sigma> # \<Gamma> \<turnstile> Var 0 : \<sigma>"
    by simp
  have "\<sigma> # \<Gamma> \<turnstile>\<^sub>CEV
      Imp (Forall \<sigma> (rename (lift_ren Suc) A))
        (subst0 (Var 0) (rename (lift_ren Suc) A))"
    using body_type_for_ui var0_type
    by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.UI)
  then show ?thesis
    by (simp add: shift_def)
qed

lemma CEV_forall_inst:
  assumes "\<sigma> # \<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile> T : \<sigma>"
  shows "\<Gamma> \<turnstile>\<^sub>CEV Imp (Forall \<sigma> A) (subst0 T A)"
  using assms
  by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.UI)

lemma CEV_modal_T_imp:
  assumes "\<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>CEV Imp (\<box>\<^sub>o A) A"
  using CEV_modal_T[OF assms] by (simp add: modal_T_def)

definition CEV_contextual_unary_equivalence_admissible :: bool where
  "CEV_contextual_unary_equivalence_admissible \<longleftrightarrow>
    (\<forall>\<Gamma> \<sigma> A F G.
      \<Gamma> \<turnstile> A : Prop \<longrightarrow>
      \<Gamma> \<turnstile> F : \<sigma> \<rightarrow>\<^sub>o Prop \<longrightarrow>
      \<Gamma> \<turnstile> G : \<sigma> \<rightarrow>\<^sub>o Prop \<longrightarrow>
      \<sigma> # \<Gamma> \<turnstile>\<^sub>CEV
        Imp (shift A)
          (App (shift F) (Var 0) \<longleftrightarrow>\<^sub>o App (shift G) (Var 0)) \<longrightarrow>
      \<Gamma> \<turnstile>\<^sub>CEV Imp A (Eq (\<sigma> \<rightarrow>\<^sub>o Prop) F G))"

lemma CEV_contextual_unary_equivalence_admissible_holds:
  "CEV_contextual_unary_equivalence_admissible"
proof (unfold CEV_contextual_unary_equivalence_admissible_def, intro allI impI)
  fix \<Gamma> \<sigma> A F G
  assume A_type: "\<Gamma> \<turnstile> A : Prop"
    and F_type: "\<Gamma> \<turnstile> F : \<sigma> \<rightarrow>\<^sub>o Prop"
    and G_type: "\<Gamma> \<turnstile> G : \<sigma> \<rightarrow>\<^sub>o Prop"
    and pointwise: "\<sigma> # \<Gamma> \<turnstile>\<^sub>CEV
      Imp (shift A)
        (App (shift F) (Var 0) \<longleftrightarrow>\<^sub>o App (shift G) (Var 0))"
  have zeta: "[\<sigma>] @ \<Gamma> \<turnstile>\<^sub>CEV
      Imp (shift_by (length [\<sigma>]) A) (zeta_body [\<sigma>] F G)"
    using pointwise by (simp add: zeta_body_def fresh_vars_def shift_by_1)
  have F_vec_type: "\<Gamma> \<turnstile> F : arrow_type [\<sigma>] Prop"
    using F_type by simp
  have G_vec_type: "\<Gamma> \<turnstile> G : arrow_type [\<sigma>] Prop"
    using G_type by simp
  have "\<Gamma> \<turnstile>\<^sub>CEV Imp A (Eq (arrow_type [\<sigma>] Prop) F G)"
    using A_type F_vec_type G_vec_type zeta
    by (rule CEV_proves.ContextVectorEquivalence)
  then show "\<Gamma> \<turnstile>\<^sub>CEV Imp A (Eq (\<sigma> \<rightarrow>\<^sub>o Prop) F G)"
    by simp
qed

lemma CEV_contextual_unary_equivalence:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile> F : \<sigma> \<rightarrow>\<^sub>o Prop"
    and "\<Gamma> \<turnstile> G : \<sigma> \<rightarrow>\<^sub>o Prop"
    and "\<sigma> # \<Gamma> \<turnstile>\<^sub>CEV
      Imp (shift A)
        (App (shift F) (Var 0) \<longleftrightarrow>\<^sub>o App (shift G) (Var 0))"
  shows "\<Gamma> \<turnstile>\<^sub>CEV Imp A (Eq (\<sigma> \<rightarrow>\<^sub>o Prop) F G)"
  using CEV_contextual_unary_equivalence_admissible_holds assms
  unfolding CEV_contextual_unary_equivalence_admissible_def by blast

lemma CEV_conj5_project1:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile> B : Prop"
    and "\<Gamma> \<turnstile> C : Prop"
    and "\<Gamma> \<turnstile> D : Prop"
    and "\<Gamma> \<turnstile> E : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>CEV
    Imp (Conj A (Conj B (Conj C (Conj D E)))) A"
proof -
  have "prop_tautology \<Gamma>
      (Imp (Conj A (Conj B (Conj C (Conj D E)))) A)"
    unfolding prop_tautology_def using assms
    by (auto intro!: has_type.Imp has_type.Conj)
  then show ?thesis
    by (rule CEV_prop_tautology)
qed

lemma CEV_conj5_project2:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile> B : Prop"
    and "\<Gamma> \<turnstile> C : Prop"
    and "\<Gamma> \<turnstile> D : Prop"
    and "\<Gamma> \<turnstile> E : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>CEV
    Imp (Conj A (Conj B (Conj C (Conj D E)))) B"
proof -
  have "prop_tautology \<Gamma>
      (Imp (Conj A (Conj B (Conj C (Conj D E)))) B)"
    unfolding prop_tautology_def using assms
    by (auto intro!: has_type.Imp has_type.Conj)
  then show ?thesis
    by (rule CEV_prop_tautology)
qed

lemma CEV_conj5_project3:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile> B : Prop"
    and "\<Gamma> \<turnstile> C : Prop"
    and "\<Gamma> \<turnstile> D : Prop"
    and "\<Gamma> \<turnstile> E : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>CEV
    Imp (Conj A (Conj B (Conj C (Conj D E)))) C"
proof -
  have "prop_tautology \<Gamma>
      (Imp (Conj A (Conj B (Conj C (Conj D E)))) C)"
    unfolding prop_tautology_def using assms
    by (auto intro!: has_type.Imp has_type.Conj)
  then show ?thesis
    by (rule CEV_prop_tautology)
qed

lemma CEV_conj5_project4:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile> B : Prop"
    and "\<Gamma> \<turnstile> C : Prop"
    and "\<Gamma> \<turnstile> D : Prop"
    and "\<Gamma> \<turnstile> E : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>CEV
    Imp (Conj A (Conj B (Conj C (Conj D E)))) D"
proof -
  have "prop_tautology \<Gamma>
      (Imp (Conj A (Conj B (Conj C (Conj D E)))) D)"
    unfolding prop_tautology_def using assms
    by (auto intro!: has_type.Imp has_type.Conj)
  then show ?thesis
    by (rule CEV_prop_tautology)
qed

lemma CEV_conj5_project5:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile> B : Prop"
    and "\<Gamma> \<turnstile> C : Prop"
    and "\<Gamma> \<turnstile> D : Prop"
    and "\<Gamma> \<turnstile> E : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>CEV
    Imp (Conj A (Conj B (Conj C (Conj D E)))) E"
proof -
  have "prop_tautology \<Gamma>
      (Imp (Conj A (Conj B (Conj C (Conj D E)))) E)"
    unfolding prop_tautology_def using assms
    by (auto intro!: has_type.Imp has_type.Conj)
  then show ?thesis
    by (rule CEV_prop_tautology)
qed

lemma CEV_imp_conj5_intro:
  assumes "\<Gamma> \<turnstile> P : Prop"
    and "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile> B : Prop"
    and "\<Gamma> \<turnstile> C : Prop"
    and "\<Gamma> \<turnstile> D : Prop"
    and "\<Gamma> \<turnstile> E : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>CEV
    Imp (Imp P A)
      (Imp (Imp P B)
        (Imp (Imp P C)
          (Imp (Imp P D)
            (Imp (Imp P E)
              (Imp P (Conj A (Conj B (Conj C (Conj D E)))))))))"
proof -
  have "prop_tautology \<Gamma>
      (Imp (Imp P A)
        (Imp (Imp P B)
          (Imp (Imp P C)
            (Imp (Imp P D)
              (Imp (Imp P E)
                (Imp P (Conj A (Conj B (Conj C (Conj D E))))))))))"
    unfolding prop_tautology_def using assms
    by (auto intro!: has_type.Imp has_type.Conj)
  then show ?thesis
    by (rule CEV_prop_tautology)
qed

lemma CEV_imp_common_conj5_intro:
  assumes "\<Gamma> \<turnstile> R : Prop"
    and "\<Gamma> \<turnstile> P : Prop"
    and "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile> B : Prop"
    and "\<Gamma> \<turnstile> C : Prop"
    and "\<Gamma> \<turnstile> D : Prop"
    and "\<Gamma> \<turnstile> E : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>CEV
    Imp (Imp R (Imp P A))
      (Imp (Imp R (Imp P B))
        (Imp (Imp R (Imp P C))
          (Imp (Imp R (Imp P D))
            (Imp (Imp R (Imp P E))
              (Imp R (Imp P (Conj A (Conj B (Conj C (Conj D E))))))))))"
proof -
  have "prop_tautology \<Gamma>
      (Imp (Imp R (Imp P A))
        (Imp (Imp R (Imp P B))
          (Imp (Imp R (Imp P C))
            (Imp (Imp R (Imp P D))
              (Imp (Imp R (Imp P E))
                (Imp R (Imp P (Conj A (Conj B (Conj C (Conj D E)))))))))))"
    unfolding prop_tautology_def using assms
    by (auto intro!: has_type.Imp has_type.Conj)
  then show ?thesis
    by (rule CEV_prop_tautology)
qed

lemma CEV_box_conj_intro_imp:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile> B : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>CEV
    Imp (\<box>\<^sub>o A) (Imp (\<box>\<^sub>o B) (\<box>\<^sub>o (Conj A B)))"
proof -
  let ?C = "Conj A B"
  have C_type: "\<Gamma> \<turnstile> ?C : Prop"
    using assms by auto
  have A_imp_BC: "\<Gamma> \<turnstile>\<^sub>CEV Imp A (Imp B ?C)"
  proof -
    have "prop_tautology \<Gamma> (Imp A (Imp B ?C))"
      unfolding prop_tautology_def
      using assms C_type by auto
    then show ?thesis
      by (rule CEV_prop_tautology)
  qed
  have box_A_imp_BC: "\<Gamma> \<turnstile>\<^sub>CEV \<box>\<^sub>o (Imp A (Imp B ?C))"
    by (rule CEV_necessitation[OF A_imp_BC])
  have K_A: "\<Gamma> \<turnstile>\<^sub>CEV modal_K A (Imp B ?C)"
    using assms(1) assms(2) C_type by (intro CEV_modal_K) auto
  have K_A_unfolded: "\<Gamma> \<turnstile>\<^sub>CEV
      Imp (\<box>\<^sub>o (Imp A (Imp B ?C)))
        (Imp (\<box>\<^sub>o A) (\<box>\<^sub>o (Imp B ?C)))"
    using K_A by (simp add: modal_K_def)
  have step_A: "\<Gamma> \<turnstile>\<^sub>CEV
      Imp (\<box>\<^sub>o A) (\<box>\<^sub>o (Imp B ?C))"
    by (rule CEV_proves.MP[OF box_A_imp_BC K_A_unfolded])
  have K_B_unfolded: "\<Gamma> \<turnstile>\<^sub>CEV
      Imp (\<box>\<^sub>o (Imp B ?C))
        (Imp (\<box>\<^sub>o B) (\<box>\<^sub>o ?C))"
    using CEV_modal_K[OF assms(2) C_type] by (simp add: modal_K_def)
  have box_A_type: "\<Gamma> \<turnstile> \<box>\<^sub>o A : Prop"
    using assms(1) by (rule typed_ObjBox)
  have box_B_type: "\<Gamma> \<turnstile> \<box>\<^sub>o B : Prop"
    using assms(2) by (rule typed_ObjBox)
  have box_BC_type: "\<Gamma> \<turnstile> \<box>\<^sub>o (Imp B ?C) : Prop"
    using assms(2) C_type by (auto intro: typed_ObjBox)
  have box_C_type: "\<Gamma> \<turnstile> \<box>\<^sub>o ?C : Prop"
    using C_type by (rule typed_ObjBox)
  have taut: "prop_tautology \<Gamma>
      (Imp
        (Imp (\<box>\<^sub>o A) (\<box>\<^sub>o (Imp B ?C)))
        (Imp
          (Imp (\<box>\<^sub>o (Imp B ?C))
            (Imp (\<box>\<^sub>o B) (\<box>\<^sub>o ?C)))
          (Imp (\<box>\<^sub>o A) (Imp (\<box>\<^sub>o B) (\<box>\<^sub>o ?C)))))"
    unfolding prop_tautology_def
    using box_A_type box_B_type box_BC_type box_C_type by auto
  have "\<Gamma> \<turnstile>\<^sub>CEV
      Imp
        (Imp (\<box>\<^sub>o A) (\<box>\<^sub>o (Imp B ?C)))
        (Imp
          (Imp (\<box>\<^sub>o (Imp B ?C))
            (Imp (\<box>\<^sub>o B) (\<box>\<^sub>o ?C)))
          (Imp (\<box>\<^sub>o A) (Imp (\<box>\<^sub>o B) (\<box>\<^sub>o ?C))))"
    by (rule CEV_prop_tautology[OF taut])
  then have "\<Gamma> \<turnstile>\<^sub>CEV
      Imp
        (Imp (\<box>\<^sub>o (Imp B ?C))
          (Imp (\<box>\<^sub>o B) (\<box>\<^sub>o ?C)))
        (Imp (\<box>\<^sub>o A) (Imp (\<box>\<^sub>o B) (\<box>\<^sub>o ?C)))"
    by (rule CEV_proves.MP[OF step_A])
  then show ?thesis
    by (rule CEV_proves.MP[OF K_B_unfolded])
qed

lemma CEV_box_conj3_from_components_imp:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile> B : Prop"
    and "\<Gamma> \<turnstile> C : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>CEV
    Imp (Conj (\<box>\<^sub>o A) (Conj (\<box>\<^sub>o B) (\<box>\<^sub>o C)))
      (\<box>\<^sub>o (Conj A (Conj B C)))"
proof -
  let ?BC = "Conj B C"
  let ?ABC = "Conj A ?BC"
  let ?P = "\<box>\<^sub>o A"
  let ?Q = "Conj (\<box>\<^sub>o B) (\<box>\<^sub>o C)"
  have BC_type: "\<Gamma> \<turnstile> ?BC : Prop"
    using assms(2,3) by auto
  have ABC_type: "\<Gamma> \<turnstile> ?ABC : Prop"
    using assms(1) BC_type by auto
  have box_BC: "\<Gamma> \<turnstile>\<^sub>CEV
      Imp (\<box>\<^sub>o B) (Imp (\<box>\<^sub>o C) (\<box>\<^sub>o ?BC))"
    using assms(2,3) by (rule CEV_box_conj_intro_imp)
  have conj_BC: "\<Gamma> \<turnstile>\<^sub>CEV
      Imp ?Q (\<box>\<^sub>o ?BC)"
    using typed_ObjBox[OF assms(2)] typed_ObjBox[OF assms(3)]
      typed_ObjBox[OF BC_type] box_BC
    by (rule CEV_curry_conj)
  have box_ABC: "\<Gamma> \<turnstile>\<^sub>CEV
      Imp (\<box>\<^sub>o A) (Imp (\<box>\<^sub>o ?BC) (\<box>\<^sub>o ?ABC))"
    using assms(1) BC_type by (rule CEV_box_conj_intro_imp)
  have P_type: "\<Gamma> \<turnstile> ?P : Prop"
    using assms(1) by (rule typed_ObjBox)
  have Q_type: "\<Gamma> \<turnstile> ?Q : Prop"
    using typed_ObjBox[OF assms(2)] typed_ObjBox[OF assms(3)] by auto
  have box_BC_type: "\<Gamma> \<turnstile> \<box>\<^sub>o ?BC : Prop"
    using BC_type by (rule typed_ObjBox)
  have box_ABC_type: "\<Gamma> \<turnstile> \<box>\<^sub>o ?ABC : Prop"
    using ABC_type by (rule typed_ObjBox)
  have step: "\<Gamma> \<turnstile>\<^sub>CEV
      Imp (Conj ?P (\<box>\<^sub>o ?BC)) (\<box>\<^sub>o ?ABC)"
    using P_type box_BC_type box_ABC_type box_ABC
    by (rule CEV_curry_conj)
  have conj_PQ_type: "\<Gamma> \<turnstile> Conj ?P ?Q : Prop"
    using P_type Q_type by auto
  have conj_P_boxBC_type: "\<Gamma> \<turnstile> Conj ?P (\<box>\<^sub>o ?BC) : Prop"
    using P_type box_BC_type by auto
  have lift: "\<Gamma> \<turnstile>\<^sub>CEV
      Imp (Conj ?P ?Q) (Conj ?P (\<box>\<^sub>o ?BC))"
  proof -
    have taut: "prop_tautology \<Gamma>
        (Imp
          (Imp ?Q (\<box>\<^sub>o ?BC))
          (Imp (Conj ?P ?Q) (Conj ?P (\<box>\<^sub>o ?BC))))"
      unfolding prop_tautology_def
      using P_type Q_type box_BC_type conj_PQ_type conj_P_boxBC_type by auto
    have "\<Gamma> \<turnstile>\<^sub>CEV
        Imp
          (Imp ?Q (\<box>\<^sub>o ?BC))
          (Imp (Conj ?P ?Q) (Conj ?P (\<box>\<^sub>o ?BC)))"
      by (rule CEV_prop_tautology[OF taut])
    then show ?thesis
      by (rule CEV_proves.MP[OF conj_BC])
  qed
  show ?thesis
    using conj_PQ_type conj_P_boxBC_type box_ABC_type lift step
    by (rule CEV_imp_trans)
qed

lemma CEV_box_conj5_from_components_imp:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile> B : Prop"
    and "\<Gamma> \<turnstile> C : Prop"
    and "\<Gamma> \<turnstile> D : Prop"
    and "\<Gamma> \<turnstile> E : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>CEV
    Imp (Conj (\<box>\<^sub>o A)
      (Conj (\<box>\<^sub>o B)
        (Conj (\<box>\<^sub>o C) (Conj (\<box>\<^sub>o D) (\<box>\<^sub>o E)))))
      (\<box>\<^sub>o (Conj (Conj A B) (Conj C (Conj D E))))"
proof -
  let ?BoxA = "\<box>\<^sub>o A"
  let ?BoxB = "\<box>\<^sub>o B"
  let ?BoxC = "\<box>\<^sub>o C"
  let ?BoxD = "\<box>\<^sub>o D"
  let ?BoxE = "\<box>\<^sub>o E"
  let ?Bundle =
    "Conj ?BoxA (Conj ?BoxB (Conj ?BoxC (Conj ?BoxD ?BoxE)))"
  let ?AB = "Conj A B"
  let ?DE = "Conj D E"
  let ?CDE = "Conj C ?DE"
  let ?ABCDE = "Conj ?AB ?CDE"
  have boxA_type: "\<Gamma> \<turnstile> ?BoxA : Prop"
    using assms(1) by (rule typed_ObjBox)
  have boxB_type: "\<Gamma> \<turnstile> ?BoxB : Prop"
    using assms(2) by (rule typed_ObjBox)
  have boxC_type: "\<Gamma> \<turnstile> ?BoxC : Prop"
    using assms(3) by (rule typed_ObjBox)
  have boxD_type: "\<Gamma> \<turnstile> ?BoxD : Prop"
    using assms(4) by (rule typed_ObjBox)
  have boxE_type: "\<Gamma> \<turnstile> ?BoxE : Prop"
    using assms(5) by (rule typed_ObjBox)
  have AB_type: "\<Gamma> \<turnstile> ?AB : Prop"
    using assms(1,2) by auto
  have DE_type: "\<Gamma> \<turnstile> ?DE : Prop"
    using assms(4,5) by auto
  have CDE_type: "\<Gamma> \<turnstile> ?CDE : Prop"
    using assms(3) DE_type by auto
  have ABCDE_type: "\<Gamma> \<turnstile> ?ABCDE : Prop"
    using AB_type CDE_type by auto
  have boxAB_type: "\<Gamma> \<turnstile> \<box>\<^sub>o ?AB : Prop"
    using AB_type by (rule typed_ObjBox)
  have boxDE_type: "\<Gamma> \<turnstile> \<box>\<^sub>o ?DE : Prop"
    using DE_type by (rule typed_ObjBox)
  have boxCDE_type: "\<Gamma> \<turnstile> \<box>\<^sub>o ?CDE : Prop"
    using CDE_type by (rule typed_ObjBox)
  have boxABCDE_type: "\<Gamma> \<turnstile> \<box>\<^sub>o ?ABCDE : Prop"
    using ABCDE_type by (rule typed_ObjBox)
  have bundle_type: "\<Gamma> \<turnstile> ?Bundle : Prop"
    using boxA_type boxB_type boxC_type boxD_type boxE_type by auto
  have local_full: "CEV_from \<Gamma> ?Bundle (\<box>\<^sub>o ?ABCDE)"
  proof -
    have local_bundle: "CEV_from \<Gamma> ?Bundle ?Bundle"
      using bundle_type by (rule CEV_from.Assumption)
    have pA: "\<Gamma> \<turnstile>\<^sub>CEV Imp ?Bundle ?BoxA"
      using boxA_type boxB_type boxC_type boxD_type boxE_type
      by (rule CEV_conj5_project1)
    have pB: "\<Gamma> \<turnstile>\<^sub>CEV Imp ?Bundle ?BoxB"
      using boxA_type boxB_type boxC_type boxD_type boxE_type
      by (rule CEV_conj5_project2)
    have pC: "\<Gamma> \<turnstile>\<^sub>CEV Imp ?Bundle ?BoxC"
      using boxA_type boxB_type boxC_type boxD_type boxE_type
      by (rule CEV_conj5_project3)
    have pD: "\<Gamma> \<turnstile>\<^sub>CEV Imp ?Bundle ?BoxD"
      using boxA_type boxB_type boxC_type boxD_type boxE_type
      by (rule CEV_conj5_project4)
    have pE: "\<Gamma> \<turnstile>\<^sub>CEV Imp ?Bundle ?BoxE"
      using boxA_type boxB_type boxC_type boxD_type boxE_type
      by (rule CEV_conj5_project5)
    have local_boxA: "CEV_from \<Gamma> ?Bundle ?BoxA"
      using local_bundle CEV_from.Theorem[OF pA] by (rule CEV_from.MP)
    have local_boxB: "CEV_from \<Gamma> ?Bundle ?BoxB"
      using local_bundle CEV_from.Theorem[OF pB] by (rule CEV_from.MP)
    have local_boxC: "CEV_from \<Gamma> ?Bundle ?BoxC"
      using local_bundle CEV_from.Theorem[OF pC] by (rule CEV_from.MP)
    have local_boxD: "CEV_from \<Gamma> ?Bundle ?BoxD"
      using local_bundle CEV_from.Theorem[OF pD] by (rule CEV_from.MP)
    have local_boxE: "CEV_from \<Gamma> ?Bundle ?BoxE"
      using local_bundle CEV_from.Theorem[OF pE] by (rule CEV_from.MP)
    have boxAB: "\<Gamma> \<turnstile>\<^sub>CEV
        Imp ?BoxA (Imp ?BoxB (\<box>\<^sub>o ?AB))"
      using assms(1,2) by (rule CEV_box_conj_intro_imp)
    have local_boxB_imp_boxAB: "CEV_from \<Gamma> ?Bundle
        (Imp ?BoxB (\<box>\<^sub>o ?AB))"
      using local_boxA CEV_from.Theorem[OF boxAB] by (rule CEV_from.MP)
    have local_boxAB: "CEV_from \<Gamma> ?Bundle (\<box>\<^sub>o ?AB)"
      using local_boxB local_boxB_imp_boxAB by (rule CEV_from.MP)
    have boxDE: "\<Gamma> \<turnstile>\<^sub>CEV
        Imp ?BoxD (Imp ?BoxE (\<box>\<^sub>o ?DE))"
      using assms(4,5) by (rule CEV_box_conj_intro_imp)
    have local_boxE_imp_boxDE: "CEV_from \<Gamma> ?Bundle
        (Imp ?BoxE (\<box>\<^sub>o ?DE))"
      using local_boxD CEV_from.Theorem[OF boxDE] by (rule CEV_from.MP)
    have local_boxDE: "CEV_from \<Gamma> ?Bundle (\<box>\<^sub>o ?DE)"
      using local_boxE local_boxE_imp_boxDE by (rule CEV_from.MP)
    have boxCDE: "\<Gamma> \<turnstile>\<^sub>CEV
        Imp ?BoxC (Imp (\<box>\<^sub>o ?DE) (\<box>\<^sub>o ?CDE))"
      using assms(3) DE_type by (rule CEV_box_conj_intro_imp)
    have local_boxDE_imp_boxCDE: "CEV_from \<Gamma> ?Bundle
        (Imp (\<box>\<^sub>o ?DE) (\<box>\<^sub>o ?CDE))"
      using local_boxC CEV_from.Theorem[OF boxCDE] by (rule CEV_from.MP)
    have local_boxCDE: "CEV_from \<Gamma> ?Bundle (\<box>\<^sub>o ?CDE)"
      using local_boxDE local_boxDE_imp_boxCDE by (rule CEV_from.MP)
    have boxABCDE: "\<Gamma> \<turnstile>\<^sub>CEV
        Imp (\<box>\<^sub>o ?AB) (Imp (\<box>\<^sub>o ?CDE) (\<box>\<^sub>o ?ABCDE))"
      using AB_type CDE_type by (rule CEV_box_conj_intro_imp)
    have local_boxCDE_imp_boxABCDE: "CEV_from \<Gamma> ?Bundle
        (Imp (\<box>\<^sub>o ?CDE) (\<box>\<^sub>o ?ABCDE))"
      using local_boxAB CEV_from.Theorem[OF boxABCDE] by (rule CEV_from.MP)
    show ?thesis
      using local_boxCDE local_boxCDE_imp_boxABCDE by (rule CEV_from.MP)
  qed
  show ?thesis
    using local_full bundle_type by (rule CEV_from_deduction)
qed

lemma caie_CEV_derivable_heq_apply:
  assumes "\<Gamma> \<turnstile> x : Ind"
    and "\<Gamma> \<turnstile> y : Ind"
  shows "caie_CEV_derivable \<Gamma> \<Delta>
    (App (caie_heq x) y \<longleftrightarrow>\<^sub>o Eq Ind y x)"
  using CEV_caie_heq_apply[OF assms] by (rule caie_CEV_derivable_of_theorem)

lemma caie_CEV_derivable_down_apply:
  assumes "\<Gamma> \<turnstile> Q : caie_classifier_ty"
    and "\<Gamma> \<turnstile> x : Ind"
  shows "caie_CEV_derivable \<Gamma> \<Delta>
    (App (Q\<^sup>\<down>\<^sub>c) x \<longleftrightarrow>\<^sub>o App Q (caie_heq x))"
  using CEV_caie_down_apply[OF assms] by (rule caie_CEV_derivable_of_theorem)

lemma caie_CEV_derivable_up_apply:
  assumes "\<Gamma> \<turnstile> P : caie_prop_ty"
    and "\<Gamma> \<turnstile> R : caie_prop_ty"
  shows "caie_CEV_derivable \<Gamma> \<Delta>
    (App (P\<^sup>\<up>\<^sub>c) R \<longleftrightarrow>\<^sub>o caie_up_body P R)"
  using CEV_caie_up_apply[OF assms] by (rule caie_CEV_derivable_of_theorem)

lemma caie_CEV_derivable_dsim:
  assumes "\<Gamma> \<turnstile> Q : caie_classifier_ty"
    and "\<Gamma> \<turnstile> Z : caie_classifier_ty"
  shows "caie_CEV_derivable \<Gamma> \<Delta>
    (Q \<sim>\<^sub>\<down>c Z \<longleftrightarrow>\<^sub>o Eq caie_prop_ty (Q\<^sup>\<down>\<^sub>c) (Z\<^sup>\<down>\<^sub>c))"
  using CEV_caie_dsim[OF assms] by (rule caie_CEV_derivable_of_theorem)

lemma caie_CEV_derivable_definitional_bridge_package:
  assumes x: "\<Gamma> \<turnstile> x : Ind"
    and y: "\<Gamma> \<turnstile> y : Ind"
    and Q: "\<Gamma> \<turnstile> Q : caie_classifier_ty"
    and Z: "\<Gamma> \<turnstile> Z : caie_classifier_ty"
    and P: "\<Gamma> \<turnstile> P : caie_prop_ty"
    and R: "\<Gamma> \<turnstile> R : caie_prop_ty"
  shows "caie_CEV_derivable \<Gamma> \<Delta>
      (App (caie_heq x) y \<longleftrightarrow>\<^sub>o Eq Ind y x)"
    and "caie_CEV_derivable \<Gamma> \<Delta>
      (App (Q\<^sup>\<down>\<^sub>c) x \<longleftrightarrow>\<^sub>o App Q (caie_heq x))"
    and "caie_CEV_derivable \<Gamma> \<Delta>
      (App (P\<^sup>\<up>\<^sub>c) R \<longleftrightarrow>\<^sub>o caie_up_body P R)"
    and "caie_CEV_derivable \<Gamma> \<Delta>
      (Q \<sim>\<^sub>\<down>c Z \<longleftrightarrow>\<^sub>o Eq caie_prop_ty (Q\<^sup>\<down>\<^sub>c) (Z\<^sup>\<down>\<^sub>c))"
proof -
  show "caie_CEV_derivable \<Gamma> \<Delta>
      (App (caie_heq x) y \<longleftrightarrow>\<^sub>o Eq Ind y x)"
    using x y by (rule caie_CEV_derivable_heq_apply)
  show "caie_CEV_derivable \<Gamma> \<Delta>
      (App (Q\<^sup>\<down>\<^sub>c) x \<longleftrightarrow>\<^sub>o App Q (caie_heq x))"
    using Q x by (rule caie_CEV_derivable_down_apply)
  show "caie_CEV_derivable \<Gamma> \<Delta>
      (App (P\<^sup>\<up>\<^sub>c) R \<longleftrightarrow>\<^sub>o caie_up_body P R)"
    using P R by (rule caie_CEV_derivable_up_apply)
  show "caie_CEV_derivable \<Gamma> \<Delta>
      (Q \<sim>\<^sub>\<down>c Z \<longleftrightarrow>\<^sub>o Eq caie_prop_ty (Q\<^sup>\<down>\<^sub>c) (Z\<^sup>\<down>\<^sub>c))"
    using Q Z by (rule caie_CEV_derivable_dsim)
qed

section \<open>Caie's Appendix C theorem statements\<close>

definition caie_Thm32 :: oterm where
  "caie_Thm32 =
    Forall caie_classifier_ty
      (Imp (caie_Name (Var 0)) (caie_phae (Var 0\<^sup>\<down>\<^sub>c)))"

definition caie_Thm33 :: oterm where
  "caie_Thm33 =
    Forall caie_prop_ty
      (Imp (caie_phae (Var 0)) (caie_Name (Var 0\<^sup>\<up>\<^sub>c)))"

definition caie_Thm34 :: oterm where
  "caie_Thm34 =
    Forall caie_prop_ty
      (Imp (caie_phae (Var 0)) (Eq caie_prop_ty (Var 0) ((Var 0\<^sup>\<up>\<^sub>c)\<^sup>\<down>\<^sub>c)))"

definition caie_Thm35 :: oterm where
  "caie_Thm35 =
    Forall caie_classifier_ty
      (Imp (caie_Name (Var 0)) (Eq caie_classifier_ty (Var 0) ((Var 0\<^sup>\<down>\<^sub>c)\<^sup>\<up>\<^sub>c)))"

definition caie_Thm36 :: oterm where
  "caie_Thm36 =
    Forall caie_prop_ty
      (Imp (caie_phae (Var 0))
        (Forall Ind
          (Imp (Eq caie_prop_ty (Var 1) (caie_heq (Var 0)))
            (Eq caie_classifier_ty (Var 1\<^sup>\<up>\<^sub>c)
              (Lam caie_prop_ty (App (Var 0) (Var 1)))))))"

definition caie_Thm37 :: oterm where
  "caie_Thm37 =
    Forall caie_prop_ty
      (Imp (Conj (caie_phae (Var 0)) (Neg (caie_hae (Var 0))))
        (Forall Ind
          (Neg (App (Var 1\<^sup>\<up>\<^sub>c) (caie_heq (Var 0))))))"

definition caie_Thm38 :: oterm where
  "caie_Thm38 =
    Forall caie_classifier_ty
      (Forall caie_classifier_ty
        (Imp (Conj (caie_WName (Var 1)) (caie_WName (Var 0)))
          ((Var 1 \<sim>\<^sub>\<down>c Var 0) \<longleftrightarrow>\<^sub>o
            \<box>\<^sub>o
              (Imp
                (Exists Ind
                  (Disj
                    (Eq caie_classifier_ty (Var 2)
                      (Lam caie_prop_ty (App (Var 0) (Var 1))))
                    (Eq caie_classifier_ty (Var 1)
                      (Lam caie_prop_ty (App (Var 0) (Var 1))))))
                (Eq caie_classifier_ty (Var 1) (Var 0))))))"

definition caie_Thm39 :: oterm where
  "caie_Thm39 =
    Forall caie_classifier_ty
      (Forall caie_classifier_ty
        (Imp (Conj (caie_Hae (Var 1)) (caie_WName (Var 0)))
          ((Var 1 \<sim>\<^sub>\<down>c Var 0) \<longleftrightarrow>\<^sub>o Eq caie_classifier_ty (Var 1) (Var 0))))"

definition caie_Thm40 :: oterm where
  "caie_Thm40 =
    Forall caie_classifier_ty
      (Imp (caie_WName (Var 0))
        (Exists caie_classifier_ty
          (Conj (caie_Name (Var 0))
            (Conj (Var 1 \<sim>\<^sub>\<down>c Var 0)
              (Forall caie_classifier_ty
                (Imp (Conj (caie_Name (Var 0)) (Var 2 \<sim>\<^sub>\<down>c Var 0))
                  (Eq caie_classifier_ty (Var 0) (Var 1))))))))"

definition caie_appendix_C_theorems :: "oterm list" where
  "caie_appendix_C_theorems =
    [caie_Thm32, caie_Thm33, caie_Thm34, caie_Thm35, caie_Thm36,
     caie_Thm37, caie_Thm38, caie_Thm39, caie_Thm40]"

lemma typed_caie_Thm32:
  "\<Gamma> \<turnstile> caie_Thm32 : Prop"
  by (rule infer_type_sound)
    (simp add: caie_Thm32_def caie_term_defs caie_type_defs lookup_def)

lemma typed_caie_Thm33:
  "\<Gamma> \<turnstile> caie_Thm33 : Prop"
  by (rule infer_type_sound)
    (simp add: caie_Thm33_def caie_term_defs caie_type_defs lookup_def)

lemma typed_caie_Thm34:
  "\<Gamma> \<turnstile> caie_Thm34 : Prop"
  by (rule infer_type_sound)
    (simp add: caie_Thm34_def caie_term_defs caie_type_defs lookup_def)

lemma typed_caie_Thm35:
  "\<Gamma> \<turnstile> caie_Thm35 : Prop"
  by (rule infer_type_sound)
    (simp add: caie_Thm35_def caie_term_defs caie_type_defs lookup_def)

lemma typed_caie_Thm36:
  "\<Gamma> \<turnstile> caie_Thm36 : Prop"
  by (rule infer_type_sound)
    (simp add: caie_Thm36_def caie_term_defs caie_type_defs lookup_def)

lemma typed_caie_Thm37:
  "\<Gamma> \<turnstile> caie_Thm37 : Prop"
  by (rule infer_type_sound)
    (simp add: caie_Thm37_def caie_term_defs caie_type_defs lookup_def)

lemma typed_caie_Thm38:
  "\<Gamma> \<turnstile> caie_Thm38 : Prop"
  by (rule infer_type_sound)
    (simp add: caie_Thm38_def caie_term_defs caie_type_defs lookup_def)

lemma typed_caie_Thm39:
  "\<Gamma> \<turnstile> caie_Thm39 : Prop"
  by (rule infer_type_sound)
    (simp add: caie_Thm39_def caie_term_defs caie_type_defs lookup_def)

lemma typed_caie_Thm40:
  "\<Gamma> \<turnstile> caie_Thm40 : Prop"
  by (rule infer_type_sound)
    (simp add: caie_Thm40_def caie_term_defs caie_type_defs lookup_def)

lemma typed_caie_appendix_C_theorem:
  assumes "A \<in> set caie_appendix_C_theorems"
  shows "\<Gamma> \<turnstile> A : Prop"
  using assms
  by (auto simp: caie_appendix_C_theorems_def
      intro: typed_caie_Thm32 typed_caie_Thm33 typed_caie_Thm34
        typed_caie_Thm35 typed_caie_Thm36 typed_caie_Thm37
        typed_caie_Thm38 typed_caie_Thm39 typed_caie_Thm40)


subsection \<open>Typed Caie assumption packages\<close>

definition caie_assumption_package :: "ctx \<Rightarrow> oterm list \<Rightarrow> bool" where
  "caie_assumption_package \<Gamma> \<Delta> \<longleftrightarrow> (\<forall>A \<in> set \<Delta>. \<Gamma> \<turnstile> A : Prop)"

lemma caie_assumption_packageD:
  assumes "caie_assumption_package \<Gamma> \<Delta>"
    and "A \<in> set \<Delta>"
  shows "\<Gamma> \<turnstile> A : Prop"
  using assms by (simp add: caie_assumption_package_def)

lemma caie_CEV_derivable_assumption:
  assumes "caie_assumption_package \<Gamma> \<Delta>"
    and "A \<in> set \<Delta>"
  shows "caie_CEV_derivable \<Gamma> \<Delta> A"
  using assms
  by (intro caie_CEV_derivable.caie_Assumption caie_assumption_packageD)

lemma caie_appendix_C_assumption_package:
  "caie_assumption_package \<Gamma> caie_appendix_C_theorems"
  unfolding caie_assumption_package_def
  by (auto intro: typed_caie_appendix_C_theorem)

lemma caie_CEV_derivable_appendix_C_assumption:
  assumes "A \<in> set caie_appendix_C_theorems"
  shows "caie_CEV_derivable \<Gamma> caie_appendix_C_theorems A"
  using caie_appendix_C_assumption_package assms
  by (rule caie_CEV_derivable_assumption)


subsection \<open>Caie-specific counterfactual and name principle packages\<close>

text \<open>
  The formulas below are not Appendix C target statements.  They are a named
  local axiom package for the additional Caie-style counterfactual and
  name/haecceity principles that are cited in the Appendix C proof
  dependencies.  This keeps the definitional bridge package separate from the
  substantive principles still needed to derive the residual targets.
\<close>

definition caie_cf_identity_principle :: oterm where
  "caie_cf_identity_principle =
    Forall Prop (ObjCF (Var 0) (Var 0))"

definition caie_cf_reciprocity_principle :: oterm where
  "caie_cf_reciprocity_principle =
    Forall Prop
      (Forall Prop
        (Forall Prop
          (Imp
            (Conj
              (Conj (ObjCF (Var 2) (Var 1)) (ObjCF (Var 1) (Var 2)))
              (ObjCF (Var 2) (Var 0)))
            (ObjCF (Var 1) (Var 0)))))"

definition caie_cf_mp_principle :: oterm where
  "caie_cf_mp_principle =
    Forall Prop
      (Forall Prop
        (Imp (ObjCF (Var 1) (Var 0)) (Imp (Var 1) (Var 0))))"

definition caie_cf_cem_principle :: oterm where
  "caie_cf_cem_principle =
    Forall Prop
      (Forall Prop
        (Disj (ObjCF (Var 1) (Var 0))
          (ObjCF (Var 1) (Neg (Var 0)))))"

definition caie_cf_nontriviality_principle :: oterm where
  "caie_cf_nontriviality_principle =
    Forall Prop
      ((Forall Prop (ObjCF (Var 1) (Var 0)))
        \<longleftrightarrow>\<^sub>o
       (\<box>\<^sub>o Neg (Var 0)))"

definition caie_cf_absorption_principle :: oterm where
  "caie_cf_absorption_principle =
    Forall Prop
      (Forall Prop
        (ObjCF (Var 1) (Var 0)
          \<longleftrightarrow>\<^sub>o
         ObjCF (Var 1) (ObjCF (Var 1) (Var 0))))"

definition caie_cf_consequent_strengthening_principle :: oterm where
  "caie_cf_consequent_strengthening_principle =
    Forall Prop
      (Forall Prop
        (Forall Prop
          (Imp (\<box>\<^sub>o Imp (Var 1) (Var 0))
            (Imp (ObjCF (Var 2) (Var 1))
              (ObjCF (Var 2) (Var 0))))))"

definition caie_counterfactual_principles :: "oterm list" where
  "caie_counterfactual_principles =
    [caie_cf_identity_principle,
     caie_cf_reciprocity_principle,
     caie_cf_mp_principle,
     caie_cf_cem_principle,
     caie_cf_nontriviality_principle,
     caie_cf_absorption_principle,
     caie_cf_consequent_strengthening_principle]"

definition caie_name_possible_haecceity_principle :: oterm where
  "caie_name_possible_haecceity_principle =
    Forall caie_classifier_ty
      (Imp (caie_Name (Var 0))
        (\<box>\<^sub>o
          (\<diamond>\<^sub>o
            (Exists Ind (App (Var 1) (caie_heq (Var 0)))))))"

definition caie_name_down_naturality_principle :: oterm where
  "caie_name_down_naturality_principle =
    Forall caie_classifier_ty
      (Imp (caie_Name (Var 0))
        (\<box>\<^sub>o
          (Forall Ind
            (Imp (App (Var 1) (caie_heq (Var 0)))
              (Eq caie_prop_ty (App caie_down_op (Var 1))
                (caie_heq (Var 0)))))))"

definition caie_name_expanded_down_phae_principle :: oterm where
  "caie_name_expanded_down_phae_principle =
    Forall caie_classifier_ty
      (Imp (caie_Name (Var 0))
        (caie_phae (Lam Ind (App (Var 1) (caie_heq (Var 0))))))"

definition caie_expanded_down_component_property :: oterm where
  "caie_expanded_down_component_property =
    Lam Ind (App (Var 2) (caie_heq (Var 0)))"

definition caie_expanded_down_possible_component :: oterm where
  "caie_expanded_down_possible_component =
    \<diamond>\<^sub>o
      (Exists Ind
        (Eq caie_prop_ty caie_expanded_down_component_property
          (caie_heq (Var 0))))"

definition caie_expanded_down_positive_persistence_component :: oterm where
  "caie_expanded_down_positive_persistence_component =
    Forall Ind
      (Imp (App caie_expanded_down_component_property (Var 0))
        (\<box>\<^sub>o App caie_expanded_down_component_property (Var 0)))"

definition caie_expanded_down_negative_persistence_component :: oterm where
  "caie_expanded_down_negative_persistence_component =
    Forall Ind
      (Imp (Neg (App caie_expanded_down_component_property (Var 0)))
        (\<box>\<^sub>o Neg (App caie_expanded_down_component_property (Var 0))))"

definition caie_expanded_down_phae_components :: oterm where
  "caie_expanded_down_phae_components =
    Conj caie_expanded_down_possible_component
      (Conj caie_expanded_down_positive_persistence_component
        caie_expanded_down_negative_persistence_component)"

definition caie_expanded_down_phae_component_boxes :: oterm where
  "caie_expanded_down_phae_component_boxes =
    Conj (\<box>\<^sub>o caie_expanded_down_possible_component)
      (Conj (\<box>\<^sub>o caie_expanded_down_positive_persistence_component)
        (\<box>\<^sub>o caie_expanded_down_negative_persistence_component))"

definition caie_name_expanded_down_phae_components_body :: oterm where
  "caie_name_expanded_down_phae_components_body =
    Imp (caie_Name (Var 0)) caie_expanded_down_phae_component_boxes"

definition caie_name_expanded_down_phae_components_principle :: oterm where
  "caie_name_expanded_down_phae_components_principle =
    Forall caie_classifier_ty caie_name_expanded_down_phae_components_body"

definition caie_phae_modal_collapse_principle :: oterm where
  "caie_phae_modal_collapse_principle =
    Forall caie_prop_ty
      (Imp (caie_phae (Var 0))
        (\<box>\<^sub>o
          (Forall Ind
            (Imp
              (\<diamond>\<^sub>o (Eq caie_prop_ty (Var 1) (caie_heq (Var 0))))
              (Eq caie_prop_ty (Var 1) (caie_heq (Var 0)))))))"

definition caie_phae_up_MC_principle :: oterm where
  "caie_phae_up_MC_principle =
    Forall caie_prop_ty
      (Imp (caie_phae (Var 0)) (\<box>\<^sub>o caie_MC (Var 0\<^sup>\<up>\<^sub>c)))"

definition caie_phae_up_AC_principle :: oterm where
  "caie_phae_up_AC_principle =
    Forall caie_prop_ty
      (Imp (caie_phae (Var 0)) (\<box>\<^sub>o caie_AC (Var 0\<^sup>\<up>\<^sub>c)))"

definition caie_phae_up_HP_principle :: oterm where
  "caie_phae_up_HP_principle =
    Forall caie_prop_ty
      (Imp (caie_phae (Var 0)) (\<box>\<^sub>o caie_HP (Var 0\<^sup>\<up>\<^sub>c)))"

definition caie_phae_up_NHP_principle :: oterm where
  "caie_phae_up_NHP_principle =
    Forall caie_prop_ty
      (Imp (caie_phae (Var 0)) (\<box>\<^sub>o caie_NHP (Var 0\<^sup>\<up>\<^sub>c)))"

definition caie_phae_up_ACF_principle :: oterm where
  "caie_phae_up_ACF_principle =
    Forall caie_prop_ty
      (Imp (caie_phae (Var 0)) (\<box>\<^sub>o caie_ACF (Var 0\<^sup>\<up>\<^sub>c)))"

definition caie_Name_components :: "oterm \<Rightarrow> oterm" where
  "caie_Name_components Q =
    Conj (Conj (caie_MC Q) (caie_AC Q))
      (Conj (caie_HP Q) (Conj (caie_NHP Q) (caie_ACF Q)))"

definition caie_Name_component_boxes :: "oterm \<Rightarrow> oterm" where
  "caie_Name_component_boxes Q =
    Conj (\<box>\<^sub>o caie_MC Q)
      (Conj (\<box>\<^sub>o caie_AC Q)
        (Conj (\<box>\<^sub>o caie_HP Q)
          (Conj (\<box>\<^sub>o caie_NHP Q) (\<box>\<^sub>o caie_ACF Q))))"

definition caie_Thm33_component_principles :: oterm where
  "caie_Thm33_component_principles =
    Conj caie_phae_up_MC_principle
      (Conj caie_phae_up_AC_principle
        (Conj caie_phae_up_HP_principle
          (Conj caie_phae_up_NHP_principle caie_phae_up_ACF_principle)))"

definition caie_phae_up_down_pointwise_principle :: oterm where
  "caie_phae_up_down_pointwise_principle =
    Forall caie_prop_ty
      (Forall Ind
        (Imp (caie_phae (Var 1))
          (App (Var 1) (Var 0)
            \<longleftrightarrow>\<^sub>o App ((Var 1\<^sup>\<up>\<^sub>c)\<^sup>\<down>\<^sub>c) (Var 0))))"

definition caie_name_down_up_pointwise_principle :: oterm where
  "caie_name_down_up_pointwise_principle =
    Forall caie_classifier_ty
      (Forall caie_prop_ty
        (Imp (caie_Name (Var 1))
          (App (Var 1) (Var 0)
            \<longleftrightarrow>\<^sub>o App ((Var 1\<^sup>\<down>\<^sub>c)\<^sup>\<up>\<^sub>c) (Var 0))))"

definition caie_haecceity_up_extensionality_principle :: oterm where
  "caie_haecceity_up_extensionality_principle =
    Forall caie_prop_ty
      (Forall Ind
        (Imp
          (Conj (caie_phae (Var 1))
            (Eq caie_prop_ty (Var 1) (caie_heq (Var 0))))
          (\<box>\<^sub>o
            (Forall caie_prop_ty
              (App (Var 2\<^sup>\<up>\<^sub>c) (Var 0)
                \<longleftrightarrow>\<^sub>o App (Var 0) (Var 1))))))"

definition caie_phae_up_hae_witness_principle :: oterm where
  "caie_phae_up_hae_witness_principle =
    Forall caie_prop_ty
      (Forall Ind
        (Imp (caie_phae (Var 1))
          (Imp (caie_up_body (Var 1) (caie_heq (Var 0)))
            (caie_hae (Var 1)))))"

definition caie_wname_possible_haecceity_principle :: oterm where
  "caie_wname_possible_haecceity_principle =
    Forall caie_classifier_ty
      (Imp (caie_WName (Var 0))
        (\<box>\<^sub>o
          (\<diamond>\<^sub>o
            (Exists Ind (App (Var 1) (caie_heq (Var 0)))))))"

definition caie_wname_down_phae_principle :: oterm where
  "caie_wname_down_phae_principle =
    Forall caie_classifier_ty
      (Imp (caie_WName (Var 0)) (caie_phae (Var 0\<^sup>\<down>\<^sub>c)))"

definition caie_wname_haecceity_classifier_principle :: oterm where
  "caie_wname_haecceity_classifier_principle =
    Forall caie_classifier_ty
      (Forall Ind
        (Imp
          (Conj (caie_WName (Var 1)) (App (Var 1) (caie_heq (Var 0))))
          (Eq caie_classifier_ty (Var 1)
            (Lam caie_prop_ty (App (Var 0) (Var 1))))))"

definition caie_hae_down_characterization_principle :: oterm where
  "caie_hae_down_characterization_principle =
    Forall caie_classifier_ty
      (Imp (caie_Hae (Var 0))
        (Exists Ind
          (\<box>\<^sub>o
            (Forall Ind
              (App (Var 2) (caie_heq (Var 0))
                \<longleftrightarrow>\<^sub>o Eq Ind (Var 0) (Var 1))))))"

definition caie_wname_dsim_extensionality_principle :: oterm where
  "caie_wname_dsim_extensionality_principle =
    Forall caie_classifier_ty
      (Forall caie_classifier_ty
        (Imp
          (Conj (caie_WName (Var 1)) (caie_WName (Var 0)))
          (Imp (Var 1 \<sim>\<^sub>\<down>c Var 0)
            (\<box>\<^sub>o
              (Forall caie_prop_ty
                (App (Var 2) (Var 0)
                  \<longleftrightarrow>\<^sub>o App (Var 1) (Var 0)))))))"

definition caie_wname_dsim_surrogacy_principle :: oterm where
  "caie_wname_dsim_surrogacy_principle =
    Forall caie_classifier_ty
      (Forall caie_classifier_ty
        (Imp
          (Conj (caie_WName (Var 1)) (caie_WName (Var 0)))
          (Eq caie_prop_ty ((Var 1)\<^sup>\<down>\<^sub>c) ((Var 0)\<^sup>\<down>\<^sub>c)
            \<longleftrightarrow>\<^sub>o
           \<box>\<^sub>o
             (Imp
               (Exists Ind
                 (Disj
                   (Eq caie_classifier_ty (Var 2)
                     (Lam caie_prop_ty (App (Var 0) (Var 1))))
                   (Eq caie_classifier_ty (Var 1)
                     (Lam caie_prop_ty (App (Var 0) (Var 1))))))
               (Eq caie_classifier_ty (Var 1) (Var 0))))))"

definition caie_hae_wname_dsim_identity_surrogacy_principle :: oterm where
  "caie_hae_wname_dsim_identity_surrogacy_principle =
    Forall caie_classifier_ty
      (Forall caie_classifier_ty
        (Imp
          (Conj (caie_Hae (Var 1)) (caie_WName (Var 0)))
          (Eq caie_prop_ty ((Var 1)\<^sup>\<down>\<^sub>c) ((Var 0)\<^sup>\<down>\<^sub>c)
            \<longleftrightarrow>\<^sub>o Eq caie_classifier_ty (Var 1) (Var 0))))"

definition caie_wname_unique_name_down_eq_surrogacy_principle :: oterm where
  "caie_wname_unique_name_down_eq_surrogacy_principle =
    Forall caie_classifier_ty
      (Imp (caie_WName (Var 0))
        (Exists caie_classifier_ty
          (Conj (caie_Name (Var 0))
            (Conj
              (Eq caie_prop_ty ((Var 1)\<^sup>\<down>\<^sub>c) ((Var 0)\<^sup>\<down>\<^sub>c))
              (Forall caie_classifier_ty
                (Imp
                  (Conj (caie_Name (Var 0))
                    (Eq caie_prop_ty ((Var 2)\<^sup>\<down>\<^sub>c) ((Var 0)\<^sup>\<down>\<^sub>c)))
                  (Eq caie_classifier_ty (Var 0) (Var 1))))))))"

definition caie_name_haecceity_principles :: "oterm list" where
  "caie_name_haecceity_principles =
    [caie_name_possible_haecceity_principle,
     caie_name_down_naturality_principle,
     caie_name_expanded_down_phae_components_principle,
     caie_phae_modal_collapse_principle,
     caie_phae_up_MC_principle,
     caie_phae_up_AC_principle,
     caie_phae_up_HP_principle,
     caie_phae_up_NHP_principle,
     caie_phae_up_ACF_principle,
     caie_phae_up_down_pointwise_principle,
     caie_name_down_up_pointwise_principle,
     caie_haecceity_up_extensionality_principle,
     caie_phae_up_hae_witness_principle,
     caie_wname_possible_haecceity_principle,
     caie_wname_down_phae_principle,
     caie_wname_haecceity_classifier_principle,
     caie_hae_down_characterization_principle,
     caie_wname_dsim_extensionality_principle,
     caie_wname_dsim_surrogacy_principle,
     caie_hae_wname_dsim_identity_surrogacy_principle,
     caie_wname_unique_name_down_eq_surrogacy_principle]"

definition caie_appendix_C_axiom_package :: "oterm list" where
  "caie_appendix_C_axiom_package =
    caie_counterfactual_principles @ caie_name_haecceity_principles"

lemma typed_caie_cf_identity_principle:
  "\<Gamma> \<turnstile> caie_cf_identity_principle : Prop"
  by (rule infer_type_sound)
    (simp add: caie_cf_identity_principle_def caie_term_defs caie_type_defs lookup_def)

lemma typed_caie_cf_reciprocity_principle:
  "\<Gamma> \<turnstile> caie_cf_reciprocity_principle : Prop"
  by (rule infer_type_sound)
    (simp add: caie_cf_reciprocity_principle_def caie_term_defs caie_type_defs lookup_def)

lemma typed_caie_cf_mp_principle:
  "\<Gamma> \<turnstile> caie_cf_mp_principle : Prop"
  by (rule infer_type_sound)
    (simp add: caie_cf_mp_principle_def caie_term_defs caie_type_defs lookup_def)

lemma typed_caie_cf_cem_principle:
  "\<Gamma> \<turnstile> caie_cf_cem_principle : Prop"
  by (rule infer_type_sound)
    (simp add: caie_cf_cem_principle_def caie_term_defs caie_type_defs lookup_def)

lemma typed_caie_cf_nontriviality_principle:
  "\<Gamma> \<turnstile> caie_cf_nontriviality_principle : Prop"
  by (rule infer_type_sound)
    (simp add: caie_cf_nontriviality_principle_def caie_term_defs caie_type_defs lookup_def)

lemma typed_caie_cf_absorption_principle:
  "\<Gamma> \<turnstile> caie_cf_absorption_principle : Prop"
  by (rule infer_type_sound)
    (simp add: caie_cf_absorption_principle_def caie_term_defs caie_type_defs lookup_def)

lemma typed_caie_cf_consequent_strengthening_principle:
  "\<Gamma> \<turnstile> caie_cf_consequent_strengthening_principle : Prop"
  by (rule infer_type_sound)
    (simp add: caie_cf_consequent_strengthening_principle_def
      caie_term_defs caie_type_defs lookup_def)

lemma typed_caie_counterfactual_principle:
  assumes "A \<in> set caie_counterfactual_principles"
  shows "\<Gamma> \<turnstile> A : Prop"
  using assms
  by (auto simp: caie_counterfactual_principles_def
      intro: typed_caie_cf_identity_principle
        typed_caie_cf_reciprocity_principle
        typed_caie_cf_mp_principle typed_caie_cf_cem_principle
        typed_caie_cf_nontriviality_principle
        typed_caie_cf_absorption_principle
        typed_caie_cf_consequent_strengthening_principle)

lemma typed_caie_name_possible_haecceity_principle:
  "\<Gamma> \<turnstile> caie_name_possible_haecceity_principle : Prop"
  by (rule infer_type_sound)
    (simp add: caie_name_possible_haecceity_principle_def
      caie_term_defs caie_type_defs lookup_def)

lemma typed_caie_name_down_naturality_principle:
  "\<Gamma> \<turnstile> caie_name_down_naturality_principle : Prop"
  by (rule infer_type_sound)
    (simp add: caie_name_down_naturality_principle_def
      caie_term_defs caie_type_defs lookup_def)

lemma typed_caie_name_expanded_down_phae_principle:
  "\<Gamma> \<turnstile> caie_name_expanded_down_phae_principle : Prop"
  by (rule infer_type_sound)
    (simp add: caie_name_expanded_down_phae_principle_def
      caie_term_defs caie_type_defs lookup_def)

lemma typed_caie_name_expanded_down_phae_components_principle:
  "\<Gamma> \<turnstile> caie_name_expanded_down_phae_components_principle : Prop"
  by (rule infer_type_sound)
    (simp add: caie_name_expanded_down_phae_components_principle_def
      caie_name_expanded_down_phae_components_body_def
      caie_expanded_down_phae_component_boxes_def
      caie_expanded_down_phae_components_def
      caie_expanded_down_possible_component_def
      caie_expanded_down_positive_persistence_component_def
      caie_expanded_down_negative_persistence_component_def
      caie_expanded_down_component_property_def
      caie_term_defs caie_type_defs lookup_def)

lemma typed_caie_phae_modal_collapse_principle:
  "\<Gamma> \<turnstile> caie_phae_modal_collapse_principle : Prop"
  by (rule infer_type_sound)
    (simp add: caie_phae_modal_collapse_principle_def
      caie_term_defs caie_type_defs lookup_def)

lemma typed_caie_phae_up_MC_principle:
  "\<Gamma> \<turnstile> caie_phae_up_MC_principle : Prop"
  by (rule infer_type_sound)
    (simp add: caie_phae_up_MC_principle_def caie_term_defs caie_type_defs lookup_def)

lemma typed_caie_phae_up_AC_principle:
  "\<Gamma> \<turnstile> caie_phae_up_AC_principle : Prop"
  by (rule infer_type_sound)
    (simp add: caie_phae_up_AC_principle_def caie_term_defs caie_type_defs lookup_def)

lemma typed_caie_phae_up_HP_principle:
  "\<Gamma> \<turnstile> caie_phae_up_HP_principle : Prop"
  by (rule infer_type_sound)
    (simp add: caie_phae_up_HP_principle_def caie_term_defs caie_type_defs lookup_def)

lemma typed_caie_phae_up_NHP_principle:
  "\<Gamma> \<turnstile> caie_phae_up_NHP_principle : Prop"
  by (rule infer_type_sound)
    (simp add: caie_phae_up_NHP_principle_def caie_term_defs caie_type_defs lookup_def)

lemma typed_caie_phae_up_ACF_principle:
  "\<Gamma> \<turnstile> caie_phae_up_ACF_principle : Prop"
  by (rule infer_type_sound)
    (simp add: caie_phae_up_ACF_principle_def caie_term_defs caie_type_defs lookup_def)

lemma typed_caie_Name_components:
  assumes "\<Gamma> \<turnstile> Q : caie_classifier_ty"
  shows "\<Gamma> \<turnstile> caie_Name_components Q : Prop"
  unfolding caie_Name_components_def
  by (intro has_type.Conj typed_caie_MC[OF assms]
      typed_caie_AC[OF assms] typed_caie_HP[OF assms]
      typed_caie_NHP[OF assms] typed_caie_ACF[OF assms])

lemma typed_caie_Name_component_boxes:
  assumes "\<Gamma> \<turnstile> Q : caie_classifier_ty"
  shows "\<Gamma> \<turnstile> caie_Name_component_boxes Q : Prop"
  unfolding caie_Name_component_boxes_def
  by (intro has_type.Conj typed_ObjBox typed_caie_MC[OF assms]
      typed_caie_AC[OF assms] typed_caie_HP[OF assms]
      typed_caie_NHP[OF assms] typed_caie_ACF[OF assms])

lemma typed_caie_Thm33_component_principles:
  "\<Gamma> \<turnstile> caie_Thm33_component_principles : Prop"
  unfolding caie_Thm33_component_principles_def
  by (intro has_type.Conj typed_caie_phae_up_MC_principle
      typed_caie_phae_up_AC_principle typed_caie_phae_up_HP_principle
      typed_caie_phae_up_NHP_principle typed_caie_phae_up_ACF_principle)

lemma typed_caie_phae_up_down_pointwise_principle:
  "\<Gamma> \<turnstile> caie_phae_up_down_pointwise_principle : Prop"
  by (rule infer_type_sound)
    (simp add: caie_phae_up_down_pointwise_principle_def
      caie_term_defs caie_type_defs lookup_def)

lemma typed_caie_name_down_up_pointwise_principle:
  "\<Gamma> \<turnstile> caie_name_down_up_pointwise_principle : Prop"
  by (rule infer_type_sound)
    (simp add: caie_name_down_up_pointwise_principle_def
      caie_term_defs caie_type_defs lookup_def)

lemma typed_caie_haecceity_up_extensionality_principle:
  "\<Gamma> \<turnstile> caie_haecceity_up_extensionality_principle : Prop"
  by (rule infer_type_sound)
    (simp add: caie_haecceity_up_extensionality_principle_def
      caie_term_defs caie_type_defs lookup_def)

lemma typed_caie_phae_up_hae_witness_principle:
  "\<Gamma> \<turnstile> caie_phae_up_hae_witness_principle : Prop"
  by (rule infer_type_sound)
    (simp add: caie_phae_up_hae_witness_principle_def
      caie_term_defs caie_type_defs lookup_def)

lemma typed_caie_wname_possible_haecceity_principle:
  "\<Gamma> \<turnstile> caie_wname_possible_haecceity_principle : Prop"
  by (rule infer_type_sound)
    (simp add: caie_wname_possible_haecceity_principle_def
      caie_term_defs caie_type_defs lookup_def)

lemma typed_caie_wname_down_phae_principle:
  "\<Gamma> \<turnstile> caie_wname_down_phae_principle : Prop"
  by (rule infer_type_sound)
    (simp add: caie_wname_down_phae_principle_def
      caie_term_defs caie_type_defs lookup_def)

lemma typed_caie_wname_haecceity_classifier_principle:
  "\<Gamma> \<turnstile> caie_wname_haecceity_classifier_principle : Prop"
  by (rule infer_type_sound)
    (simp add: caie_wname_haecceity_classifier_principle_def
      caie_term_defs caie_type_defs lookup_def)

lemma typed_caie_hae_down_characterization_principle:
  "\<Gamma> \<turnstile> caie_hae_down_characterization_principle : Prop"
  by (rule infer_type_sound)
    (simp add: caie_hae_down_characterization_principle_def
      caie_term_defs caie_type_defs lookup_def)

lemma typed_caie_wname_dsim_extensionality_principle:
  "\<Gamma> \<turnstile> caie_wname_dsim_extensionality_principle : Prop"
  by (rule infer_type_sound)
    (simp add: caie_wname_dsim_extensionality_principle_def
      caie_term_defs caie_type_defs lookup_def)

lemma typed_caie_wname_dsim_surrogacy_principle:
  "\<Gamma> \<turnstile> caie_wname_dsim_surrogacy_principle : Prop"
  by (rule infer_type_sound)
    (simp add: caie_wname_dsim_surrogacy_principle_def
      caie_term_defs caie_type_defs lookup_def)

lemma typed_caie_hae_wname_dsim_identity_surrogacy_principle:
  "\<Gamma> \<turnstile> caie_hae_wname_dsim_identity_surrogacy_principle : Prop"
  by (rule infer_type_sound)
    (simp add: caie_hae_wname_dsim_identity_surrogacy_principle_def
      caie_term_defs caie_type_defs lookup_def)

lemma typed_caie_wname_unique_name_down_eq_surrogacy_principle:
  "\<Gamma> \<turnstile> caie_wname_unique_name_down_eq_surrogacy_principle : Prop"
  by (rule infer_type_sound)
    (simp add: caie_wname_unique_name_down_eq_surrogacy_principle_def
      caie_term_defs caie_type_defs lookup_def)

lemma typed_caie_name_haecceity_principle:
  assumes "A \<in> set caie_name_haecceity_principles"
  shows "\<Gamma> \<turnstile> A : Prop"
  using assms
  by (auto simp: caie_name_haecceity_principles_def
      intro: typed_caie_name_possible_haecceity_principle
        typed_caie_name_down_naturality_principle
        typed_caie_name_expanded_down_phae_components_principle
        typed_caie_phae_modal_collapse_principle
        typed_caie_phae_up_MC_principle typed_caie_phae_up_AC_principle
        typed_caie_phae_up_HP_principle typed_caie_phae_up_NHP_principle
        typed_caie_phae_up_ACF_principle
        typed_caie_phae_up_down_pointwise_principle
        typed_caie_name_down_up_pointwise_principle
        typed_caie_haecceity_up_extensionality_principle
        typed_caie_phae_up_hae_witness_principle
        typed_caie_wname_possible_haecceity_principle
        typed_caie_wname_down_phae_principle
        typed_caie_wname_haecceity_classifier_principle
        typed_caie_hae_down_characterization_principle
        typed_caie_wname_dsim_extensionality_principle
        typed_caie_wname_dsim_surrogacy_principle
        typed_caie_hae_wname_dsim_identity_surrogacy_principle
        typed_caie_wname_unique_name_down_eq_surrogacy_principle)

lemma typed_caie_appendix_C_axiom:
  assumes "A \<in> set caie_appendix_C_axiom_package"
  shows "\<Gamma> \<turnstile> A : Prop"
  using assms
  by (auto simp: caie_appendix_C_axiom_package_def
      intro: typed_caie_counterfactual_principle
        typed_caie_name_haecceity_principle)

lemma caie_counterfactual_assumption_package:
  "caie_assumption_package \<Gamma> caie_counterfactual_principles"
  unfolding caie_assumption_package_def
  by (auto intro: typed_caie_counterfactual_principle)

lemma caie_name_haecceity_assumption_package:
  "caie_assumption_package \<Gamma> caie_name_haecceity_principles"
  unfolding caie_assumption_package_def
  by (auto intro: typed_caie_name_haecceity_principle)

lemma caie_appendix_C_axiom_package_typed:
  "caie_assumption_package \<Gamma> caie_appendix_C_axiom_package"
  unfolding caie_assumption_package_def
  by (auto intro: typed_caie_appendix_C_axiom)

lemma caie_CEV_derivable_appendix_C_axiom:
  assumes "A \<in> set caie_appendix_C_axiom_package"
  shows "caie_CEV_derivable \<Gamma> caie_appendix_C_axiom_package A"
  using caie_appendix_C_axiom_package_typed assms
  by (rule caie_CEV_derivable_assumption)

lemma caie_CEV_derivable_name_haecceity_axiom:
  assumes "A \<in> set caie_name_haecceity_principles"
  shows "caie_CEV_derivable \<Gamma> caie_appendix_C_axiom_package A"
proof -
  have "A \<in> set caie_appendix_C_axiom_package"
    using assms by (simp add: caie_appendix_C_axiom_package_def)
  then show ?thesis
    by (rule caie_CEV_derivable_appendix_C_axiom)
qed

lemma caie_appendix_C_axiom_package_definitional_bridge_package:
  assumes x: "\<Gamma> \<turnstile> x : Ind"
    and y: "\<Gamma> \<turnstile> y : Ind"
    and Q: "\<Gamma> \<turnstile> Q : caie_classifier_ty"
    and Z: "\<Gamma> \<turnstile> Z : caie_classifier_ty"
    and P: "\<Gamma> \<turnstile> P : caie_prop_ty"
    and R: "\<Gamma> \<turnstile> R : caie_prop_ty"
  shows "caie_CEV_derivable \<Gamma> caie_appendix_C_axiom_package
      (App (caie_heq x) y \<longleftrightarrow>\<^sub>o Eq Ind y x)"
    and "caie_CEV_derivable \<Gamma> caie_appendix_C_axiom_package
      (App (Q\<^sup>\<down>\<^sub>c) x \<longleftrightarrow>\<^sub>o App Q (caie_heq x))"
    and "caie_CEV_derivable \<Gamma> caie_appendix_C_axiom_package
      (App (P\<^sup>\<up>\<^sub>c) R \<longleftrightarrow>\<^sub>o caie_up_body P R)"
    and "caie_CEV_derivable \<Gamma> caie_appendix_C_axiom_package
      (Q \<sim>\<^sub>\<down>c Z \<longleftrightarrow>\<^sub>o Eq caie_prop_ty (Q\<^sup>\<down>\<^sub>c) (Z\<^sup>\<down>\<^sub>c))"
  using x y Q Z P R
  by (rule caie_CEV_derivable_definitional_bridge_package)+

lemma typed_caie_expanded_down_possible_component:
  "caie_classifier_ty # \<Gamma> \<turnstile> caie_expanded_down_possible_component : Prop"
  by (rule infer_type_sound)
    (simp add: caie_expanded_down_possible_component_def
      caie_expanded_down_component_property_def
      caie_term_defs caie_type_defs lookup_def)

lemma typed_caie_expanded_down_positive_persistence_component:
  "caie_classifier_ty # \<Gamma> \<turnstile>
    caie_expanded_down_positive_persistence_component : Prop"
  by (rule infer_type_sound)
    (simp add: caie_expanded_down_positive_persistence_component_def
      caie_expanded_down_component_property_def
      caie_term_defs caie_type_defs lookup_def)

lemma typed_caie_expanded_down_negative_persistence_component:
  "caie_classifier_ty # \<Gamma> \<turnstile>
    caie_expanded_down_negative_persistence_component : Prop"
  by (rule infer_type_sound)
    (simp add: caie_expanded_down_negative_persistence_component_def
      caie_expanded_down_component_property_def
      caie_term_defs caie_type_defs lookup_def)

lemma typed_caie_expanded_down_phae_components:
  "caie_classifier_ty # \<Gamma> \<turnstile> caie_expanded_down_phae_components : Prop"
  by (rule infer_type_sound)
    (simp add: caie_expanded_down_phae_components_def
      caie_expanded_down_possible_component_def
      caie_expanded_down_positive_persistence_component_def
      caie_expanded_down_negative_persistence_component_def
      caie_expanded_down_component_property_def
      caie_term_defs caie_type_defs lookup_def)

lemma typed_caie_expanded_down_phae_component_boxes:
  "caie_classifier_ty # \<Gamma> \<turnstile> caie_expanded_down_phae_component_boxes : Prop"
  by (rule infer_type_sound)
    (simp add: caie_expanded_down_phae_component_boxes_def
      caie_expanded_down_possible_component_def
      caie_expanded_down_positive_persistence_component_def
      caie_expanded_down_negative_persistence_component_def
      caie_expanded_down_component_property_def
      caie_term_defs caie_type_defs lookup_def)

lemma typed_caie_expanded_down_lambda:
  "caie_classifier_ty # \<Gamma> \<turnstile>
    Lam Ind (App (Var 1) (caie_heq (Var 0))) : caie_prop_ty"
  by (rule infer_type_sound)
    (simp add: caie_term_defs caie_type_defs lookup_def)

lemma typed_caie_name_expanded_down_phae_body:
  "caie_classifier_ty # \<Gamma> \<turnstile>
    Imp (caie_Name (Var 0))
      (caie_phae (Lam Ind (App (Var 1) (caie_heq (Var 0))))) : Prop"
  by (rule infer_type_sound)
    (simp add: caie_term_defs caie_type_defs lookup_def)

lemma beta_eta_caie_expanded_down_phae_body:
  "beta_eta_equiv (caie_classifier_ty # \<Gamma>) Prop
    (caie_phae (Lam Ind (App (Var 1) (caie_heq (Var 0)))))
    (\<box>\<^sub>o caie_expanded_down_phae_components)"
proof -
  let ?D = "Lam Ind (App (Var 1) (caie_heq (Var 0)))"
  let ?B = "\<box>\<^sub>o caie_expanded_down_phae_components"
  have left_type: "caie_classifier_ty # \<Gamma> \<turnstile> caie_phae ?D : Prop"
    using typed_caie_expanded_down_lambda by (rule typed_caie_phae)
  have right_type: "caie_classifier_ty # \<Gamma> \<turnstile> ?B : Prop"
    using typed_caie_expanded_down_phae_components by (rule typed_ObjBox)
  have step: "compatible_step beta_contract (caie_phae ?D) ?B"
  proof -
    let ?Body =
      "\<box>\<^sub>o
        (Conj
          (\<diamond>\<^sub>o
            (Exists Ind
              (Eq caie_prop_ty (Var 1) (caie_heq (Var 0)))))
          (Conj
            (Forall Ind
              (Imp (App (Var 1) (Var 0))
                (\<box>\<^sub>o App (Var 1) (Var 0))))
            (Forall Ind
              (Imp (Neg (App (Var 1) (Var 0)))
                (\<box>\<^sub>o Neg (App (Var 1) (Var 0)))))))"
    have subst_eq: "subst0 ?D ?Body = ?B"
      by (simp add: subst0_def caie_expanded_down_phae_components_def
          caie_expanded_down_possible_component_def
          caie_expanded_down_positive_persistence_component_def
          caie_expanded_down_negative_persistence_component_def
          caie_expanded_down_component_property_def
          caie_heq_def shift_def ObjBox_def ObjDiamond_def ObjTrue_def)
    have "compatible_step beta_contract (App caie_phae_op ?D)
        (subst0 ?D
          ?Body)"
      unfolding caie_phae_op_def
      by (intro compatible_step.root beta_contract.beta)
    then show ?thesis
      using subst_eq by simp
  qed
  show ?thesis
    using left_type right_type step by (rule beta_eta_equiv.Beta)
qed

lemma CEV_caie_expanded_down_phae_from_component_boxes:
  "caie_classifier_ty # \<Gamma> \<turnstile>\<^sub>CEV
    Imp caie_expanded_down_phae_component_boxes
      (caie_phae (Lam Ind (App (Var 1) (caie_heq (Var 0)))))"
proof -
  let ?D = "Lam Ind (App (Var 1) (caie_heq (Var 0)))"
  let ?BoxComponents = "\<box>\<^sub>o caie_expanded_down_phae_components"
  have poss_type: "caie_classifier_ty # \<Gamma> \<turnstile>
      caie_expanded_down_possible_component : Prop"
    by (rule typed_caie_expanded_down_possible_component)
  have pos_type: "caie_classifier_ty # \<Gamma> \<turnstile>
      caie_expanded_down_positive_persistence_component : Prop"
    by (rule typed_caie_expanded_down_positive_persistence_component)
  have neg_type: "caie_classifier_ty # \<Gamma> \<turnstile>
      caie_expanded_down_negative_persistence_component : Prop"
    by (rule typed_caie_expanded_down_negative_persistence_component)
  have boxes_type: "caie_classifier_ty # \<Gamma> \<turnstile>
      caie_expanded_down_phae_component_boxes : Prop"
    by (rule typed_caie_expanded_down_phae_component_boxes)
  have box_components_type: "caie_classifier_ty # \<Gamma> \<turnstile>
      ?BoxComponents : Prop"
    using typed_caie_expanded_down_phae_components by (rule typed_ObjBox)
  have phae_type: "caie_classifier_ty # \<Gamma> \<turnstile> caie_phae ?D : Prop"
    using typed_caie_expanded_down_lambda by (rule typed_caie_phae)
  have assemble: "caie_classifier_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp caie_expanded_down_phae_component_boxes ?BoxComponents"
    unfolding caie_expanded_down_phae_component_boxes_def
      caie_expanded_down_phae_components_def
    using poss_type pos_type neg_type
    by (rule CEV_box_conj3_from_components_imp)
  have beta: "caie_classifier_ty # \<Gamma> \<turnstile>\<^sub>CEV
      (caie_phae ?D \<longleftrightarrow>\<^sub>o ?BoxComponents)"
    using beta_eta_caie_expanded_down_phae_body
    by (rule CEV_beta_eta_equiv)
  have box_to_phae: "caie_classifier_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp ?BoxComponents (caie_phae ?D)"
    using phae_type box_components_type beta by (rule CEV_beta_right_imp)
  show ?thesis
    using boxes_type box_components_type phae_type assemble box_to_phae
    by (rule CEV_imp_trans)
qed

lemma CEV_caie_name_expanded_down_phae_body_from_components:
  "caie_classifier_ty # \<Gamma> \<turnstile>\<^sub>CEV
    Imp caie_name_expanded_down_phae_components_body
      (Imp (caie_Name (Var 0))
        (caie_phae (Lam Ind (App (Var 1) (caie_heq (Var 0))))))"
proof -
  let ?Name = "caie_Name (Var 0)"
  let ?D = "Lam Ind (App (Var 1) (caie_heq (Var 0)))"
  have name_type: "caie_classifier_ty # \<Gamma> \<turnstile> ?Name : Prop"
    by (rule infer_type_sound)
      (simp add: caie_term_defs caie_type_defs lookup_def)
  have boxes_type: "caie_classifier_ty # \<Gamma> \<turnstile>
      caie_expanded_down_phae_component_boxes : Prop"
    by (rule typed_caie_expanded_down_phae_component_boxes)
  have phae_type: "caie_classifier_ty # \<Gamma> \<turnstile> caie_phae ?D : Prop"
    using typed_caie_expanded_down_lambda by (rule typed_caie_phae)
  have boxes_to_phae: "caie_classifier_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp caie_expanded_down_phae_component_boxes (caie_phae ?D)"
    by (rule CEV_caie_expanded_down_phae_from_component_boxes)
  have lifted: "caie_classifier_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp (Imp ?Name caie_expanded_down_phae_component_boxes)
        (Imp ?Name (caie_phae ?D))"
    using name_type boxes_type phae_type boxes_to_phae
    by (rule CEV_imp_lift_right)
  then show ?thesis
    by (simp add: caie_name_expanded_down_phae_components_body_def)
qed

lemma CEV_caie_name_expanded_down_phae_from_components:
  "\<Gamma> \<turnstile>\<^sub>CEV
    Imp caie_name_expanded_down_phae_components_principle
      caie_name_expanded_down_phae_principle"
proof -
  let ?P = "caie_name_expanded_down_phae_components_principle"
  let ?D = "Lam Ind (App (Var 1) (caie_heq (Var 0)))"
  let ?Q = "Imp (caie_Name (Var 0)) (caie_phae ?D)"
  have P_type: "\<Gamma> \<turnstile> ?P : Prop"
    by (rule typed_caie_name_expanded_down_phae_components_principle)
  have shifted_P_type: "caie_classifier_ty # \<Gamma> \<turnstile> shift ?P : Prop"
    using P_type by (rule weakening_front)
  have body_type: "caie_classifier_ty # \<Gamma> \<turnstile>
      caie_name_expanded_down_phae_components_body : Prop"
    by (rule infer_type_sound)
      (simp add: caie_name_expanded_down_phae_components_body_def
        caie_expanded_down_phae_component_boxes_def
        caie_expanded_down_possible_component_def
        caie_expanded_down_positive_persistence_component_def
        caie_expanded_down_negative_persistence_component_def
        caie_expanded_down_component_property_def
        caie_term_defs caie_type_defs lookup_def)
  have Q_type: "caie_classifier_ty # \<Gamma> \<turnstile> ?Q : Prop"
    by (rule typed_caie_name_expanded_down_phae_body)
  have body_type_for_ui: "caie_classifier_ty # caie_classifier_ty # \<Gamma> \<turnstile>
      rename (lift_ren Suc) caie_name_expanded_down_phae_components_body : Prop"
    using body_type by (rule weakening_after_front)
  have var0_type: "caie_classifier_ty # \<Gamma> \<turnstile> Var 0 : caie_classifier_ty"
    by (simp add: lookup_def)
  have ui_raw: "caie_classifier_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp (Forall caie_classifier_ty
            (rename (lift_ren Suc) caie_name_expanded_down_phae_components_body))
        (subst0 (Var 0)
          (rename (lift_ren Suc) caie_name_expanded_down_phae_components_body))"
    using body_type_for_ui var0_type
    by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.UI)
  have ui: "caie_classifier_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp (shift ?P) caie_name_expanded_down_phae_components_body"
    using ui_raw
    by (simp add: caie_name_expanded_down_phae_components_principle_def
      shift_def)
  have body_to_Q: "caie_classifier_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp caie_name_expanded_down_phae_components_body ?Q"
    by (rule CEV_caie_name_expanded_down_phae_body_from_components)
  have inst_imp: "caie_classifier_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp (shift ?P) ?Q"
    using shifted_P_type body_type Q_type ui body_to_Q by (rule CEV_imp_trans)
  have gen: "\<Gamma> \<turnstile>\<^sub>CEV
      Imp ?P (Forall caie_classifier_ty ?Q)"
    using P_type Q_type inst_imp by (rule CEV_proves.Gen)
  then show ?thesis
    by (simp add: caie_name_expanded_down_phae_principle_def)
qed

lemma beta_eta_caie_Name:
  assumes "\<Gamma> \<turnstile> Q : caie_classifier_ty"
  shows "beta_eta_equiv \<Gamma> Prop
    (caie_Name Q) (\<box>\<^sub>o caie_Name_components Q)"
proof -
  have left_type: "\<Gamma> \<turnstile> caie_Name Q : Prop"
    using assms by (rule typed_caie_Name)
  have right_type: "\<Gamma> \<turnstile> \<box>\<^sub>o caie_Name_components Q : Prop"
    using typed_caie_Name_components[OF assms] by (rule typed_ObjBox)
  have step: "compatible_step beta_contract
      (caie_Name Q) (\<box>\<^sub>o caie_Name_components Q)"
  proof -
    let ?Body =
      "\<box>\<^sub>o
        (Conj
          (Conj (App caie_MC_op (Var 0)) (App caie_AC_op (Var 0)))
          (Conj (App caie_HP_op (Var 0))
            (Conj (App caie_NHP_op (Var 0)) (App caie_ACF_op (Var 0)))))"
    have two: "(2::nat) = Suc (Suc 0)"
      by simp
    have three: "(3::nat) = Suc (Suc (Suc 0))"
      by simp
    have subst_eq:
        "subst0 Q ?Body = \<box>\<^sub>o caie_Name_components Q"
      by (simp add: subst0_def caie_Name_components_def
          caie_term_defs two three)
    have "compatible_step beta_contract (App caie_Name_op Q) (subst0 Q ?Body)"
      unfolding caie_Name_op_def
      by (intro compatible_step.root beta_contract.beta)
    then show ?thesis
      using subst_eq by simp
  qed
  show ?thesis
    using left_type right_type step by (rule beta_eta_equiv.Beta)
qed

lemma CEV_caie_Name_from_component_boxes:
  assumes "\<Gamma> \<turnstile> Q : caie_classifier_ty"
  shows "\<Gamma> \<turnstile>\<^sub>CEV
    Imp (caie_Name_component_boxes Q) (caie_Name Q)"
proof -
  have mc_type: "\<Gamma> \<turnstile> caie_MC Q : Prop"
    using assms by (rule typed_caie_MC)
  have ac_type: "\<Gamma> \<turnstile> caie_AC Q : Prop"
    using assms by (rule typed_caie_AC)
  have hp_type: "\<Gamma> \<turnstile> caie_HP Q : Prop"
    using assms by (rule typed_caie_HP)
  have nhp_type: "\<Gamma> \<turnstile> caie_NHP Q : Prop"
    using assms by (rule typed_caie_NHP)
  have acf_type: "\<Gamma> \<turnstile> caie_ACF Q : Prop"
    using assms by (rule typed_caie_ACF)
  have boxes_type: "\<Gamma> \<turnstile> caie_Name_component_boxes Q : Prop"
    using assms by (rule typed_caie_Name_component_boxes)
  have box_components_type: "\<Gamma> \<turnstile> \<box>\<^sub>o caie_Name_components Q : Prop"
    using typed_caie_Name_components[OF assms] by (rule typed_ObjBox)
  have name_type: "\<Gamma> \<turnstile> caie_Name Q : Prop"
    using assms by (rule typed_caie_Name)
  have assemble: "\<Gamma> \<turnstile>\<^sub>CEV
      Imp (caie_Name_component_boxes Q) (\<box>\<^sub>o caie_Name_components Q)"
    unfolding caie_Name_component_boxes_def caie_Name_components_def
    using mc_type ac_type hp_type nhp_type acf_type
    by (rule CEV_box_conj5_from_components_imp)
  have beta: "\<Gamma> \<turnstile>\<^sub>CEV
      (caie_Name Q \<longleftrightarrow>\<^sub>o \<box>\<^sub>o caie_Name_components Q)"
    using beta_eta_caie_Name[OF assms] by (rule CEV_beta_eta_equiv)
  have box_to_name: "\<Gamma> \<turnstile>\<^sub>CEV
      Imp (\<box>\<^sub>o caie_Name_components Q) (caie_Name Q)"
    using name_type box_components_type beta by (rule CEV_beta_right_imp)
  show ?thesis
    using boxes_type box_components_type name_type assemble box_to_name
    by (rule CEV_imp_trans)
qed

lemma CEV_caie_Thm33_from_component_principles:
  "\<Gamma> \<turnstile>\<^sub>CEV
    Imp caie_Thm33_component_principles caie_Thm33"
proof -
  let ?P = "caie_Thm33_component_principles"
  let ?Q = "Var 0\<^sup>\<up>\<^sub>c"
  let ?Phi = "caie_phae (Var 0)"
  let ?MC = "\<box>\<^sub>o caie_MC ?Q"
  let ?AC = "\<box>\<^sub>o caie_AC ?Q"
  let ?HP = "\<box>\<^sub>o caie_HP ?Q"
  let ?NHP = "\<box>\<^sub>o caie_NHP ?Q"
  let ?ACF = "\<box>\<^sub>o caie_ACF ?Q"
  let ?MC_body = "Imp ?Phi ?MC"
  let ?AC_body = "Imp ?Phi ?AC"
  let ?HP_body = "Imp ?Phi ?HP"
  let ?NHP_body = "Imp ?Phi ?NHP"
  let ?ACF_body = "Imp ?Phi ?ACF"
  let ?Boxes = "caie_Name_component_boxes ?Q"
  let ?Body = "Imp ?Phi (caie_Name ?Q)"
  have P_type: "\<Gamma> \<turnstile> ?P : Prop"
    by (rule typed_caie_Thm33_component_principles)
  have shifted_P_type: "caie_prop_ty # \<Gamma> \<turnstile> shift ?P : Prop"
    using P_type by (rule weakening_front)
  have var0_type: "caie_prop_ty # \<Gamma> \<turnstile> Var 0 : caie_prop_ty"
    by simp
  have Q_type: "caie_prop_ty # \<Gamma> \<turnstile> ?Q : caie_classifier_ty"
    using var0_type by (rule typed_caie_up)
  have Phi_type: "caie_prop_ty # \<Gamma> \<turnstile> ?Phi : Prop"
    using var0_type by (rule typed_caie_phae)
  have MC_type: "caie_prop_ty # \<Gamma> \<turnstile> ?MC : Prop"
    using typed_caie_MC[OF Q_type] by (rule typed_ObjBox)
  have AC_type: "caie_prop_ty # \<Gamma> \<turnstile> ?AC : Prop"
    using typed_caie_AC[OF Q_type] by (rule typed_ObjBox)
  have HP_type: "caie_prop_ty # \<Gamma> \<turnstile> ?HP : Prop"
    using typed_caie_HP[OF Q_type] by (rule typed_ObjBox)
  have NHP_type: "caie_prop_ty # \<Gamma> \<turnstile> ?NHP : Prop"
    using typed_caie_NHP[OF Q_type] by (rule typed_ObjBox)
  have ACF_type: "caie_prop_ty # \<Gamma> \<turnstile> ?ACF : Prop"
    using typed_caie_ACF[OF Q_type] by (rule typed_ObjBox)
  have MC_body_type: "caie_prop_ty # \<Gamma> \<turnstile> ?MC_body : Prop"
    using Phi_type MC_type by auto
  have AC_body_type: "caie_prop_ty # \<Gamma> \<turnstile> ?AC_body : Prop"
    using Phi_type AC_type by auto
  have HP_body_type: "caie_prop_ty # \<Gamma> \<turnstile> ?HP_body : Prop"
    using Phi_type HP_type by auto
  have NHP_body_type: "caie_prop_ty # \<Gamma> \<turnstile> ?NHP_body : Prop"
    using Phi_type NHP_type by auto
  have ACF_body_type: "caie_prop_ty # \<Gamma> \<turnstile> ?ACF_body : Prop"
    using Phi_type ACF_type by auto
  have boxes_type: "caie_prop_ty # \<Gamma> \<turnstile> ?Boxes : Prop"
    using Q_type by (rule typed_caie_Name_component_boxes)
  have boxes_body_type: "caie_prop_ty # \<Gamma> \<turnstile> Imp ?Phi ?Boxes : Prop"
    using Phi_type boxes_type by auto
  have name_type: "caie_prop_ty # \<Gamma> \<turnstile> caie_Name ?Q : Prop"
    using Q_type by (rule typed_caie_Name)
  have body_type: "caie_prop_ty # \<Gamma> \<turnstile> ?Body : Prop"
    using Phi_type name_type by auto
  have shifted_MC_principle_type:
      "caie_prop_ty # \<Gamma> \<turnstile> shift caie_phae_up_MC_principle : Prop"
    using typed_caie_phae_up_MC_principle by (rule weakening_front)
  have shifted_AC_principle_type:
      "caie_prop_ty # \<Gamma> \<turnstile> shift caie_phae_up_AC_principle : Prop"
    using typed_caie_phae_up_AC_principle by (rule weakening_front)
  have shifted_HP_principle_type:
      "caie_prop_ty # \<Gamma> \<turnstile> shift caie_phae_up_HP_principle : Prop"
    using typed_caie_phae_up_HP_principle by (rule weakening_front)
  have shifted_NHP_principle_type:
      "caie_prop_ty # \<Gamma> \<turnstile> shift caie_phae_up_NHP_principle : Prop"
    using typed_caie_phae_up_NHP_principle by (rule weakening_front)
  have shifted_ACF_principle_type:
      "caie_prop_ty # \<Gamma> \<turnstile> shift caie_phae_up_ACF_principle : Prop"
    using typed_caie_phae_up_ACF_principle by (rule weakening_front)
  have proj_MC: "caie_prop_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp (shift ?P) (shift caie_phae_up_MC_principle)"
  proof -
    have "caie_prop_ty # \<Gamma> \<turnstile>\<^sub>CEV
        Imp
          (Conj (shift caie_phae_up_MC_principle)
            (Conj (shift caie_phae_up_AC_principle)
              (Conj (shift caie_phae_up_HP_principle)
                (Conj (shift caie_phae_up_NHP_principle)
                  (shift caie_phae_up_ACF_principle)))))
          (shift caie_phae_up_MC_principle)"
      using shifted_MC_principle_type shifted_AC_principle_type
        shifted_HP_principle_type shifted_NHP_principle_type
        shifted_ACF_principle_type
      by (rule CEV_conj5_project1)
    then show ?thesis
      by (simp add: caie_Thm33_component_principles_def shift_def)
  qed
  have proj_AC: "caie_prop_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp (shift ?P) (shift caie_phae_up_AC_principle)"
  proof -
    have "caie_prop_ty # \<Gamma> \<turnstile>\<^sub>CEV
        Imp
          (Conj (shift caie_phae_up_MC_principle)
            (Conj (shift caie_phae_up_AC_principle)
              (Conj (shift caie_phae_up_HP_principle)
                (Conj (shift caie_phae_up_NHP_principle)
                  (shift caie_phae_up_ACF_principle)))))
          (shift caie_phae_up_AC_principle)"
      using shifted_MC_principle_type shifted_AC_principle_type
        shifted_HP_principle_type shifted_NHP_principle_type
        shifted_ACF_principle_type
      by (rule CEV_conj5_project2)
    then show ?thesis
      by (simp add: caie_Thm33_component_principles_def shift_def)
  qed
  have proj_HP: "caie_prop_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp (shift ?P) (shift caie_phae_up_HP_principle)"
  proof -
    have "caie_prop_ty # \<Gamma> \<turnstile>\<^sub>CEV
        Imp
          (Conj (shift caie_phae_up_MC_principle)
            (Conj (shift caie_phae_up_AC_principle)
              (Conj (shift caie_phae_up_HP_principle)
                (Conj (shift caie_phae_up_NHP_principle)
                  (shift caie_phae_up_ACF_principle)))))
          (shift caie_phae_up_HP_principle)"
      using shifted_MC_principle_type shifted_AC_principle_type
        shifted_HP_principle_type shifted_NHP_principle_type
        shifted_ACF_principle_type
      by (rule CEV_conj5_project3)
    then show ?thesis
      by (simp add: caie_Thm33_component_principles_def shift_def)
  qed
  have proj_NHP: "caie_prop_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp (shift ?P) (shift caie_phae_up_NHP_principle)"
  proof -
    have "caie_prop_ty # \<Gamma> \<turnstile>\<^sub>CEV
        Imp
          (Conj (shift caie_phae_up_MC_principle)
            (Conj (shift caie_phae_up_AC_principle)
              (Conj (shift caie_phae_up_HP_principle)
                (Conj (shift caie_phae_up_NHP_principle)
                  (shift caie_phae_up_ACF_principle)))))
          (shift caie_phae_up_NHP_principle)"
      using shifted_MC_principle_type shifted_AC_principle_type
        shifted_HP_principle_type shifted_NHP_principle_type
        shifted_ACF_principle_type
      by (rule CEV_conj5_project4)
    then show ?thesis
      by (simp add: caie_Thm33_component_principles_def shift_def)
  qed
  have proj_ACF: "caie_prop_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp (shift ?P) (shift caie_phae_up_ACF_principle)"
  proof -
    have "caie_prop_ty # \<Gamma> \<turnstile>\<^sub>CEV
        Imp
          (Conj (shift caie_phae_up_MC_principle)
            (Conj (shift caie_phae_up_AC_principle)
              (Conj (shift caie_phae_up_HP_principle)
                (Conj (shift caie_phae_up_NHP_principle)
                  (shift caie_phae_up_ACF_principle)))))
          (shift caie_phae_up_ACF_principle)"
      using shifted_MC_principle_type shifted_AC_principle_type
        shifted_HP_principle_type shifted_NHP_principle_type
        shifted_ACF_principle_type
      by (rule CEV_conj5_project5)
    then show ?thesis
      by (simp add: caie_Thm33_component_principles_def shift_def)
  qed
  have ui_MC: "caie_prop_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp (shift caie_phae_up_MC_principle) ?MC_body"
    using CEV_shifted_forall_inst_Var0[OF MC_body_type]
    by (simp add: caie_phae_up_MC_principle_def)
  have ui_AC: "caie_prop_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp (shift caie_phae_up_AC_principle) ?AC_body"
    using CEV_shifted_forall_inst_Var0[OF AC_body_type]
    by (simp add: caie_phae_up_AC_principle_def)
  have ui_HP: "caie_prop_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp (shift caie_phae_up_HP_principle) ?HP_body"
    using CEV_shifted_forall_inst_Var0[OF HP_body_type]
    by (simp add: caie_phae_up_HP_principle_def)
  have ui_NHP: "caie_prop_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp (shift caie_phae_up_NHP_principle) ?NHP_body"
    using CEV_shifted_forall_inst_Var0[OF NHP_body_type]
    by (simp add: caie_phae_up_NHP_principle_def)
  have ui_ACF: "caie_prop_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp (shift caie_phae_up_ACF_principle) ?ACF_body"
    using CEV_shifted_forall_inst_Var0[OF ACF_body_type]
    by (simp add: caie_phae_up_ACF_principle_def)
  have MC_from_P: "caie_prop_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp (shift ?P) ?MC_body"
    using shifted_P_type shifted_MC_principle_type MC_body_type
      proj_MC ui_MC
    by (rule CEV_imp_trans)
  have AC_from_P: "caie_prop_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp (shift ?P) ?AC_body"
    using shifted_P_type shifted_AC_principle_type AC_body_type
      proj_AC ui_AC
    by (rule CEV_imp_trans)
  have HP_from_P: "caie_prop_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp (shift ?P) ?HP_body"
    using shifted_P_type shifted_HP_principle_type HP_body_type
      proj_HP ui_HP
    by (rule CEV_imp_trans)
  have NHP_from_P: "caie_prop_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp (shift ?P) ?NHP_body"
    using shifted_P_type shifted_NHP_principle_type NHP_body_type
      proj_NHP ui_NHP
    by (rule CEV_imp_trans)
  have ACF_from_P: "caie_prop_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp (shift ?P) ?ACF_body"
    using shifted_P_type shifted_ACF_principle_type ACF_body_type
      proj_ACF ui_ACF
    by (rule CEV_imp_trans)
  have component_intro: "caie_prop_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp (Imp (shift ?P) ?MC_body)
        (Imp (Imp (shift ?P) ?AC_body)
          (Imp (Imp (shift ?P) ?HP_body)
            (Imp (Imp (shift ?P) ?NHP_body)
              (Imp (Imp (shift ?P) ?ACF_body)
                (Imp (shift ?P) (Imp ?Phi ?Boxes))))))"
    using shifted_P_type Phi_type MC_type AC_type HP_type NHP_type ACF_type
    unfolding caie_Name_component_boxes_def
    by (rule CEV_imp_common_conj5_intro)
  have step1: "caie_prop_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp (Imp (shift ?P) ?AC_body)
        (Imp (Imp (shift ?P) ?HP_body)
          (Imp (Imp (shift ?P) ?NHP_body)
            (Imp (Imp (shift ?P) ?ACF_body)
              (Imp (shift ?P) (Imp ?Phi ?Boxes)))))"
    using MC_from_P component_intro by (rule CEV_proves.MP)
  have step2: "caie_prop_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp (Imp (shift ?P) ?HP_body)
        (Imp (Imp (shift ?P) ?NHP_body)
          (Imp (Imp (shift ?P) ?ACF_body)
            (Imp (shift ?P) (Imp ?Phi ?Boxes))))"
    using AC_from_P step1 by (rule CEV_proves.MP)
  have step3: "caie_prop_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp (Imp (shift ?P) ?NHP_body)
        (Imp (Imp (shift ?P) ?ACF_body)
          (Imp (shift ?P) (Imp ?Phi ?Boxes)))"
    using HP_from_P step2 by (rule CEV_proves.MP)
  have step4: "caie_prop_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp (Imp (shift ?P) ?ACF_body)
        (Imp (shift ?P) (Imp ?Phi ?Boxes))"
    using NHP_from_P step3 by (rule CEV_proves.MP)
  have boxes_from_P: "caie_prop_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp (shift ?P) (Imp ?Phi ?Boxes)"
    using ACF_from_P step4 by (rule CEV_proves.MP)
  have name_from_boxes: "caie_prop_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp ?Boxes (caie_Name ?Q)"
    using Q_type by (rule CEV_caie_Name_from_component_boxes)
  have lifted_name: "caie_prop_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp (Imp ?Phi ?Boxes) (Imp ?Phi (caie_Name ?Q))"
    using Phi_type boxes_type name_type name_from_boxes
    by (rule CEV_imp_lift_right)
  have inst_imp: "caie_prop_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp (shift ?P) ?Body"
    using shifted_P_type boxes_body_type body_type boxes_from_P lifted_name
    by (rule CEV_imp_trans)
  have gen: "\<Gamma> \<turnstile>\<^sub>CEV
      Imp ?P (Forall caie_prop_ty ?Body)"
    using P_type body_type inst_imp by (rule CEV_proves.Gen)
  then show ?thesis
    by (simp add: caie_Thm33_def)
qed

lemma CEV_caie_haecceity_up_extensionality_instance:
  "Ind # caie_prop_ty # \<Gamma> \<turnstile>\<^sub>CEV
    Imp (shift (shift caie_haecceity_up_extensionality_principle))
      (Imp
        (Conj (caie_phae (Var 1))
          (Eq caie_prop_ty (Var 1) (caie_heq (Var 0))))
        (\<box>\<^sub>o
          (Forall caie_prop_ty
            (App (Var 2\<^sup>\<up>\<^sub>c) (Var 0)
              \<longleftrightarrow>\<^sub>o App (Var 0) (Var 1)))))"
proof -
  let ?OuterBody =
    "Forall Ind
      (Imp
        (Conj (caie_phae (Var 1))
          (Eq caie_prop_ty (Var 1) (caie_heq (Var 0))))
        (\<box>\<^sub>o
          (Forall caie_prop_ty
            (App (Var 2\<^sup>\<up>\<^sub>c) (Var 0)
              \<longleftrightarrow>\<^sub>o App (Var 0) (Var 1)))))"
  let ?LiftedOuterBody =
    "rename (lift_ren Suc) (rename (lift_ren Suc) ?OuterBody)"
  let ?ForallX =
    "Forall Ind
      (Imp
        (Conj (caie_phae (Var 2))
          (Eq caie_prop_ty (Var 2) (caie_heq (Var 0))))
        (\<box>\<^sub>o
          (Forall caie_prop_ty
            (App (Var 3\<^sup>\<up>\<^sub>c) (Var 0)
              \<longleftrightarrow>\<^sub>o App (Var 0) (Var 1)))))"
  let ?Inst =
    "Imp
      (Conj (caie_phae (Var 1))
        (Eq caie_prop_ty (Var 1) (caie_heq (Var 0))))
      (\<box>\<^sub>o
        (Forall caie_prop_ty
          (App (Var 2\<^sup>\<up>\<^sub>c) (Var 0)
            \<longleftrightarrow>\<^sub>o App (Var 0) (Var 1))))"
  have outer_body_type: "caie_prop_ty # \<Gamma> \<turnstile> ?OuterBody : Prop"
    by (rule infer_type_sound)
      (simp add: caie_term_defs caie_type_defs lookup_def)
  have lifted_outer_body_once_type:
      "caie_prop_ty # caie_prop_ty # \<Gamma> \<turnstile>
        rename (lift_ren Suc) ?OuterBody : Prop"
    using outer_body_type by (rule weakening_after_front)
  have lifted_outer_body_type:
      "caie_prop_ty # Ind # caie_prop_ty # \<Gamma> \<turnstile>
        ?LiftedOuterBody : Prop"
    using lifted_outer_body_once_type by (rule weakening_after_front)
  have var1_type: "Ind # caie_prop_ty # \<Gamma> \<turnstile> Var 1 : caie_prop_ty"
    by simp
  have outer_raw: "Ind # caie_prop_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp (Forall caie_prop_ty ?LiftedOuterBody)
        (subst0 (Var 1) ?LiftedOuterBody)"
    using lifted_outer_body_type var1_type by (rule CEV_forall_inst)
  have outer_ui: "Ind # caie_prop_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp (shift (shift caie_haecceity_up_extensionality_principle))
        ?ForallX"
    using outer_raw
    by (simp add: caie_haecceity_up_extensionality_principle_def
      caie_term_defs caie_type_defs shift_def subst0_def eval_nat_numeral)
  have inner_body_type: "Ind # Ind # caie_prop_ty # \<Gamma> \<turnstile>
      (Imp
        (Conj (caie_phae (Var 2))
          (Eq caie_prop_ty (Var 2) (caie_heq (Var 0))))
        (\<box>\<^sub>o
          (Forall caie_prop_ty
            (App (Var 3\<^sup>\<up>\<^sub>c) (Var 0)
              \<longleftrightarrow>\<^sub>o App (Var 0) (Var 1))))) : Prop"
    by (rule infer_type_sound)
      (simp add: caie_term_defs caie_type_defs lookup_def)
  have var0_type: "Ind # caie_prop_ty # \<Gamma> \<turnstile> Var 0 : Ind"
    by simp
  have inner_raw: "Ind # caie_prop_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp ?ForallX
        (subst0 (Var 0)
          (Imp
            (Conj (caie_phae (Var 2))
              (Eq caie_prop_ty (Var 2) (caie_heq (Var 0))))
            (\<box>\<^sub>o
              (Forall caie_prop_ty
                (App (Var 3\<^sup>\<up>\<^sub>c) (Var 0)
                  \<longleftrightarrow>\<^sub>o App (Var 0) (Var 1))))))"
    using inner_body_type var0_type by (rule CEV_forall_inst)
  have inner_ui: "Ind # caie_prop_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp ?ForallX ?Inst"
    using inner_raw
    by (simp add: caie_term_defs caie_type_defs subst0_def eval_nat_numeral)
  have shifted_principle_type:
      "Ind # caie_prop_ty # \<Gamma> \<turnstile>
        shift (shift caie_haecceity_up_extensionality_principle) : Prop"
    using typed_caie_haecceity_up_extensionality_principle
    by (intro weakening_front)
  have forallX_type: "Ind # caie_prop_ty # \<Gamma> \<turnstile> ?ForallX : Prop"
    by (rule infer_type_sound)
      (simp add: caie_term_defs caie_type_defs lookup_def)
  have inst_type: "Ind # caie_prop_ty # \<Gamma> \<turnstile> ?Inst : Prop"
    by (rule infer_type_sound)
      (simp add: caie_term_defs caie_type_defs lookup_def)
  show ?thesis
    using shifted_principle_type forallX_type inst_type outer_ui inner_ui
    by (rule CEV_imp_trans)
qed

lemma CEV_caie_haecceity_up_extensionality_pointwise_instance:
  "caie_prop_ty # Ind # caie_prop_ty # \<Gamma> \<turnstile>\<^sub>CEV
    Imp (shift (shift (shift caie_haecceity_up_extensionality_principle)))
      (Imp
        (Conj (caie_phae (Var 2))
          (Eq caie_prop_ty (Var 2) (caie_heq (Var 1))))
        (App (Var 2\<^sup>\<up>\<^sub>c) (Var 0)
          \<longleftrightarrow>\<^sub>o App (Var 0) (Var 1)))"
proof -
  let ?OuterBody =
    "Forall Ind
      (Imp
        (Conj (caie_phae (Var 1))
          (Eq caie_prop_ty (Var 1) (caie_heq (Var 0))))
        (\<box>\<^sub>o
          (Forall caie_prop_ty
            (App (Var 2\<^sup>\<up>\<^sub>c) (Var 0)
              \<longleftrightarrow>\<^sub>o App (Var 0) (Var 1)))))"
  let ?LiftedOuterBody =
    "rename (lift_ren Suc)
      (rename (lift_ren Suc) (rename (lift_ren Suc) ?OuterBody))"
  let ?ForallX =
    "Forall Ind
      (Imp
        (Conj (caie_phae (Var 3))
          (Eq caie_prop_ty (Var 3) (caie_heq (Var 0))))
        (\<box>\<^sub>o
          (Forall caie_prop_ty
            (App (Var 4\<^sup>\<up>\<^sub>c) (Var 0)
              \<longleftrightarrow>\<^sub>o App (Var 0) (Var 1)))))"
  let ?Q =
    "Conj (caie_phae (Var 2))
      (Eq caie_prop_ty (Var 2) (caie_heq (Var 1)))"
  let ?BoxForall =
    "\<box>\<^sub>o
      (Forall caie_prop_ty
        (App (Var 3\<^sup>\<up>\<^sub>c) (Var 0)
          \<longleftrightarrow>\<^sub>o App (Var 0) (Var 2)))"
  let ?Point =
    "App (Var 2\<^sup>\<up>\<^sub>c) (Var 0)
      \<longleftrightarrow>\<^sub>o App (Var 0) (Var 1)"
  have outer_body_type:
      "caie_prop_ty # caie_prop_ty # Ind # caie_prop_ty # \<Gamma> \<turnstile>
        ?LiftedOuterBody : Prop"
    by (rule infer_type_sound)
      (simp add: caie_term_defs caie_type_defs lookup_def eval_nat_numeral)
  have var2_type:
      "caie_prop_ty # Ind # caie_prop_ty # \<Gamma> \<turnstile> Var 2 : caie_prop_ty"
    by (simp add: lookup_def)
  have outer_raw: "caie_prop_ty # Ind # caie_prop_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp (Forall caie_prop_ty ?LiftedOuterBody)
        (subst0 (Var 2) ?LiftedOuterBody)"
    using outer_body_type var2_type by (rule CEV_forall_inst)
  have outer_ui: "caie_prop_ty # Ind # caie_prop_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp (shift (shift (shift caie_haecceity_up_extensionality_principle)))
        ?ForallX"
    using outer_raw
    by (simp add: caie_haecceity_up_extensionality_principle_def
        caie_term_defs caie_type_defs shift_def subst0_def eval_nat_numeral)
  have inner_body_type: "Ind # caie_prop_ty # Ind # caie_prop_ty # \<Gamma> \<turnstile>
      (Imp
        (Conj (caie_phae (Var 3))
          (Eq caie_prop_ty (Var 3) (caie_heq (Var 0))))
        (\<box>\<^sub>o
          (Forall caie_prop_ty
            (App (Var 4\<^sup>\<up>\<^sub>c) (Var 0)
              \<longleftrightarrow>\<^sub>o App (Var 0) (Var 1))))) : Prop"
    by (rule infer_type_sound)
      (simp add: caie_term_defs caie_type_defs lookup_def eval_nat_numeral)
  have var1_type:
      "caie_prop_ty # Ind # caie_prop_ty # \<Gamma> \<turnstile> Var 1 : Ind"
    by (simp add: lookup_def)
  have inner_raw: "caie_prop_ty # Ind # caie_prop_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp ?ForallX
        (subst0 (Var 1)
          (Imp
            (Conj (caie_phae (Var 3))
              (Eq caie_prop_ty (Var 3) (caie_heq (Var 0))))
            (\<box>\<^sub>o
              (Forall caie_prop_ty
                (App (Var 4\<^sup>\<up>\<^sub>c) (Var 0)
                  \<longleftrightarrow>\<^sub>o App (Var 0) (Var 1))))))"
    using inner_body_type var1_type by (rule CEV_forall_inst)
  have inner_ui: "caie_prop_ty # Ind # caie_prop_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp ?ForallX (Imp ?Q ?BoxForall)"
    using inner_raw
    by (simp add: caie_term_defs caie_type_defs subst0_def eval_nat_numeral)
  have P_type: "caie_prop_ty # Ind # caie_prop_ty # \<Gamma> \<turnstile>
      shift (shift (shift caie_haecceity_up_extensionality_principle)) : Prop"
    using typed_caie_haecceity_up_extensionality_principle
    by (intro weakening_front)
  have forallX_type: "caie_prop_ty # Ind # caie_prop_ty # \<Gamma> \<turnstile>
      ?ForallX : Prop"
    by (rule infer_type_sound)
      (simp add: caie_term_defs caie_type_defs lookup_def eval_nat_numeral)
  have Q_type: "caie_prop_ty # Ind # caie_prop_ty # \<Gamma> \<turnstile> ?Q : Prop"
    by (rule infer_type_sound)
      (simp add: caie_term_defs caie_type_defs lookup_def eval_nat_numeral)
  have box_forall_type: "caie_prop_ty # Ind # caie_prop_ty # \<Gamma> \<turnstile>
      ?BoxForall : Prop"
    by (rule infer_type_sound)
      (simp add: caie_term_defs caie_type_defs lookup_def eval_nat_numeral)
  have point_type: "caie_prop_ty # Ind # caie_prop_ty # \<Gamma> \<turnstile>
      ?Point : Prop"
    by (rule infer_type_sound)
      (simp add: caie_term_defs caie_type_defs lookup_def eval_nat_numeral)
  have inst_type: "caie_prop_ty # Ind # caie_prop_ty # \<Gamma> \<turnstile>
      Imp ?Q ?BoxForall : Prop"
    using Q_type box_forall_type by auto
  have inst_box: "caie_prop_ty # Ind # caie_prop_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp (shift (shift (shift caie_haecceity_up_extensionality_principle)))
        (Imp ?Q ?BoxForall)"
    using P_type forallX_type inst_type outer_ui inner_ui
    by (rule CEV_imp_trans)
  have forall_type: "caie_prop_ty # Ind # caie_prop_ty # \<Gamma> \<turnstile>
      Forall caie_prop_ty
        (App (Var 3\<^sup>\<up>\<^sub>c) (Var 0)
          \<longleftrightarrow>\<^sub>o App (Var 0) (Var 2)) : Prop"
    by (rule infer_type_sound)
      (simp add: caie_term_defs caie_type_defs lookup_def eval_nat_numeral)
  have modal_step: "caie_prop_ty # Ind # caie_prop_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp ?BoxForall
        (Forall caie_prop_ty
          (App (Var 3\<^sup>\<up>\<^sub>c) (Var 0)
            \<longleftrightarrow>\<^sub>o App (Var 0) (Var 2)))"
    using forall_type by (rule CEV_modal_T_imp)
  have point_body_type:
      "caie_prop_ty # caie_prop_ty # Ind # caie_prop_ty # \<Gamma> \<turnstile>
        (App (Var 3\<^sup>\<up>\<^sub>c) (Var 0)
          \<longleftrightarrow>\<^sub>o App (Var 0) (Var 2)) : Prop"
    by (rule infer_type_sound)
      (simp add: caie_term_defs caie_type_defs lookup_def eval_nat_numeral)
  have var0_type:
      "caie_prop_ty # Ind # caie_prop_ty # \<Gamma> \<turnstile> Var 0 : caie_prop_ty"
    by (simp add: lookup_def)
  have forall_raw: "caie_prop_ty # Ind # caie_prop_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp
        (Forall caie_prop_ty
          (App (Var 3\<^sup>\<up>\<^sub>c) (Var 0)
            \<longleftrightarrow>\<^sub>o App (Var 0) (Var 2)))
        (subst0 (Var 0)
          (App (Var 3\<^sup>\<up>\<^sub>c) (Var 0)
            \<longleftrightarrow>\<^sub>o App (Var 0) (Var 2)))"
    using point_body_type var0_type
    by (rule CEV_forall_inst)
  have forall_inst: "caie_prop_ty # Ind # caie_prop_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp
        (Forall caie_prop_ty
          (App (Var 3\<^sup>\<up>\<^sub>c) (Var 0)
            \<longleftrightarrow>\<^sub>o App (Var 0) (Var 2)))
        ?Point"
    using forall_raw
    by (simp add: caie_term_defs caie_type_defs subst0_def eval_nat_numeral)
  have box_to_point: "caie_prop_ty # Ind # caie_prop_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp ?BoxForall ?Point"
    using box_forall_type forall_type point_type modal_step forall_inst
    by (rule CEV_imp_trans)
  have lift_Q: "caie_prop_ty # Ind # caie_prop_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp (Imp ?Q ?BoxForall) (Imp ?Q ?Point)"
    using Q_type box_forall_type point_type box_to_point
    by (rule CEV_imp_lift_right)
  have point_imp_type: "caie_prop_ty # Ind # caie_prop_ty # \<Gamma> \<turnstile>
      Imp ?Q ?Point : Prop"
    using Q_type point_type by auto
  show ?thesis
    using P_type inst_type point_imp_type inst_box lift_Q
    by (rule CEV_imp_trans)
qed

lemma beta_eta_caie_Thm36_classifier_lambda_point:
  "beta_eta_equiv (caie_prop_ty # Ind # caie_prop_ty # \<Gamma>) Prop
    (App (shift (Lam caie_prop_ty (App (Var 0) (Var 1)))) (Var 0))
    (App (Var 0) (Var 1))"
proof -
  have left_type: "caie_prop_ty # Ind # caie_prop_ty # \<Gamma> \<turnstile>
      App (shift (Lam caie_prop_ty (App (Var 0) (Var 1)))) (Var 0) : Prop"
    by (rule infer_type_sound)
      (simp add: caie_term_defs caie_type_defs lookup_def)
  have right_type: "caie_prop_ty # Ind # caie_prop_ty # \<Gamma> \<turnstile>
      App (Var 0) (Var 1) : Prop"
    by (rule infer_type_sound)
      (simp add: caie_term_defs caie_type_defs lookup_def)
  have step: "compatible_step beta_contract
      (App (shift (Lam caie_prop_ty (App (Var 0) (Var 1)))) (Var 0))
      (App (Var 0) (Var 1))"
  proof -
    have "compatible_step beta_contract
        (App (Lam caie_prop_ty (rename (lift_ren Suc) (App (Var 0) (Var 1)))) (Var 0))
        (subst0 (Var 0) (rename (lift_ren Suc) (App (Var 0) (Var 1))))"
      by (intro compatible_step.root beta_contract.beta)
    then show ?thesis
      by (simp add: subst0_def shift_def)
  qed
  show ?thesis
    using left_type right_type step by (rule beta_eta_equiv.Beta)
qed

lemma CEV_caie_Thm36_classifier_lambda_point:
  "caie_prop_ty # Ind # caie_prop_ty # \<Gamma> \<turnstile>\<^sub>CEV
    (App (shift (Lam caie_prop_ty (App (Var 0) (Var 1)))) (Var 0)
      \<longleftrightarrow>\<^sub>o App (Var 0) (Var 1))"
  using beta_eta_caie_Thm36_classifier_lambda_point
  by (rule CEV_beta_eta_equiv)

lemma CEV_caie_Thm36_contextual_unary_premise:
  "caie_prop_ty # Ind # caie_prop_ty # \<Gamma> \<turnstile>\<^sub>CEV
    Imp
      (shift
        (Conj (shift (shift caie_haecceity_up_extensionality_principle))
          (Conj (caie_phae (Var 1))
            (Eq caie_prop_ty (Var 1) (caie_heq (Var 0))))))
      (App (shift (Var 1\<^sup>\<up>\<^sub>c)) (Var 0)
        \<longleftrightarrow>\<^sub>o
       App (shift (Lam caie_prop_ty (App (Var 0) (Var 1)))) (Var 0))"
proof -
  let ?P = "shift (shift (shift caie_haecceity_up_extensionality_principle))"
  let ?Phi = "caie_phae (Var 2)"
  let ?E = "Eq caie_prop_ty (Var 2) (caie_heq (Var 1))"
  let ?Q = "Conj ?Phi ?E"
  let ?X = "App (Var 2\<^sup>\<up>\<^sub>c) (Var 0)"
  let ?Y = "App (shift (Lam caie_prop_ty (App (Var 0) (Var 1)))) (Var 0)"
  let ?Z = "App (Var 0) (Var 1)"
  let ?XZ = "?X \<longleftrightarrow>\<^sub>o ?Z"
  let ?XY = "?X \<longleftrightarrow>\<^sub>o ?Y"
  have P_type: "caie_prop_ty # Ind # caie_prop_ty # \<Gamma> \<turnstile> ?P : Prop"
    using typed_caie_haecceity_up_extensionality_principle
    by (intro weakening_front)
  have Q_type: "caie_prop_ty # Ind # caie_prop_ty # \<Gamma> \<turnstile> ?Q : Prop"
    by (rule infer_type_sound)
      (simp add: caie_term_defs caie_type_defs lookup_def eval_nat_numeral)
  have X_type: "caie_prop_ty # Ind # caie_prop_ty # \<Gamma> \<turnstile> ?X : Prop"
    by (rule infer_type_sound)
      (simp add: caie_term_defs caie_type_defs lookup_def eval_nat_numeral)
  have Y_type: "caie_prop_ty # Ind # caie_prop_ty # \<Gamma> \<turnstile> ?Y : Prop"
    by (rule infer_type_sound)
      (simp add: caie_term_defs caie_type_defs lookup_def eval_nat_numeral)
  have Z_type: "caie_prop_ty # Ind # caie_prop_ty # \<Gamma> \<turnstile> ?Z : Prop"
    by (rule infer_type_sound)
      (simp add: caie_term_defs caie_type_defs lookup_def eval_nat_numeral)
  have XZ_type: "caie_prop_ty # Ind # caie_prop_ty # \<Gamma> \<turnstile> ?XZ : Prop"
    using X_type Z_type by auto
  have XY_type: "caie_prop_ty # Ind # caie_prop_ty # \<Gamma> \<turnstile> ?XY : Prop"
    using X_type Y_type by auto
  have pointwise: "caie_prop_ty # Ind # caie_prop_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp ?P (Imp ?Q ?XZ)"
    by (rule CEV_caie_haecceity_up_extensionality_pointwise_instance)
  have grouped_pointwise: "caie_prop_ty # Ind # caie_prop_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp (Conj ?P ?Q) ?XZ"
    using P_type Q_type XZ_type pointwise by (rule CEV_curry_conj)
  have grouped_assumption_type: "caie_prop_ty # Ind # caie_prop_ty # \<Gamma> \<turnstile>
      Conj ?P ?Q : Prop"
    using P_type Q_type by auto
  have beta: "caie_prop_ty # Ind # caie_prop_ty # \<Gamma> \<turnstile>\<^sub>CEV
      (?Y \<longleftrightarrow>\<^sub>o ?Z)"
    by (rule CEV_caie_Thm36_classifier_lambda_point)
  have replace_right: "caie_prop_ty # Ind # caie_prop_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp ?XZ ?XY"
    using X_type Y_type Z_type beta by (rule CEV_bicond_replace_right)
  have grouped_target: "caie_prop_ty # Ind # caie_prop_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp (Conj ?P ?Q) ?XY"
    using grouped_assumption_type XZ_type XY_type grouped_pointwise replace_right
    by (rule CEV_imp_trans)
  then show ?thesis
    by (simp add: caie_term_defs caie_type_defs shift_def eval_nat_numeral)
qed

lemma shift_caie_Thm36_combined_antecedent[simp]:
  "shift
    (Conj (shift caie_haecceity_up_extensionality_principle)
      (caie_phae (Var 0))) =
   Conj (shift (shift caie_haecceity_up_extensionality_principle))
      (caie_phae (Var 1))"
  by (simp add: shift_def)

lemma CEV_caie_Thm36_from_haecceity_up_extensionality:
  "\<Gamma> \<turnstile>\<^sub>CEV
    Imp caie_haecceity_up_extensionality_principle caie_Thm36"
proof -
  let ?Hax = "caie_haecceity_up_extensionality_principle"
  let ?Hax_shift = "shift ?Hax"
  let ?Hax_shift2 = "shift (shift ?Hax)"
  let ?Phi_outer = "caie_phae (Var 0)"
  let ?Phi_inner = "caie_phae (Var 1)"
  let ?E = "Eq caie_prop_ty (Var 1) (caie_heq (Var 0))"
  let ?F = "Var 1\<^sup>\<up>\<^sub>c"
  let ?G = "Lam caie_prop_ty (App (Var 0) (Var 1))"
  let ?R = "Eq caie_classifier_ty ?F ?G"
  let ?ConjPhiE = "Conj ?Phi_inner ?E"
  let ?H = "Conj ?Hax_shift2 ?ConjPhiE"
  let ?Body = "Imp ?E ?R"
  let ?Combined = "Conj ?Hax_shift ?Phi_outer"
  let ?ForallX = "Forall Ind ?Body"
  let ?OuterBody = "Imp ?Phi_outer ?ForallX"
  have P2_type0: "Ind # caie_prop_ty # \<Gamma> \<turnstile> ?Hax_shift2 : Prop"
    using typed_caie_haecceity_up_extensionality_principle
    by (intro weakening_front)
  have Phi_type0: "Ind # caie_prop_ty # \<Gamma> \<turnstile> ?Phi_inner : Prop"
    by (rule infer_type_sound)
      (simp add: caie_term_defs caie_type_defs lookup_def eval_nat_numeral)
  have E_type0: "Ind # caie_prop_ty # \<Gamma> \<turnstile> ?E : Prop"
    by (rule infer_type_sound)
      (simp add: caie_term_defs caie_type_defs lookup_def eval_nat_numeral)
  have conjPhiE_type0: "Ind # caie_prop_ty # \<Gamma> \<turnstile> ?ConjPhiE : Prop"
    using Phi_type0 E_type0 by auto
  have H_type: "Ind # caie_prop_ty # \<Gamma> \<turnstile> ?H : Prop"
    using P2_type0 conjPhiE_type0 by auto
  have F_arrow_type:
      "Ind # caie_prop_ty # \<Gamma> \<turnstile> ?F : caie_prop_ty \<rightarrow>\<^sub>o Prop"
    by (rule infer_type_sound)
      (simp add: caie_term_defs caie_type_defs lookup_def eval_nat_numeral)
  have G_arrow_type:
      "Ind # caie_prop_ty # \<Gamma> \<turnstile> ?G : caie_prop_ty \<rightarrow>\<^sub>o Prop"
    by (rule infer_type_sound)
      (simp add: caie_term_defs caie_type_defs lookup_def eval_nat_numeral)
  have contextual_premise: "caie_prop_ty # Ind # caie_prop_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp (shift ?H)
        (App (shift ?F) (Var 0) \<longleftrightarrow>\<^sub>o App (shift ?G) (Var 0))"
    by (rule CEV_caie_Thm36_contextual_unary_premise)
  have closure_raw: "Ind # caie_prop_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp ?H (Eq (caie_prop_ty \<rightarrow>\<^sub>o Prop) ?F ?G)"
    using H_type F_arrow_type G_arrow_type contextual_premise
    by (rule CEV_contextual_unary_equivalence)
  have closure: "Ind # caie_prop_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp ?H ?R"
    using closure_raw by (simp add: caie_classifier_ty_def)
  have P2_type: "Ind # caie_prop_ty # \<Gamma> \<turnstile> ?Hax_shift2 : Prop"
    using typed_caie_haecceity_up_extensionality_principle
    by (intro weakening_front)
  have Phi_type: "Ind # caie_prop_ty # \<Gamma> \<turnstile> ?Phi_inner : Prop"
    by (rule infer_type_sound)
      (simp add: caie_term_defs caie_type_defs lookup_def eval_nat_numeral)
  have E_type: "Ind # caie_prop_ty # \<Gamma> \<turnstile> ?E : Prop"
    by (rule infer_type_sound)
      (simp add: caie_term_defs caie_type_defs lookup_def eval_nat_numeral)
  have R_type: "Ind # caie_prop_ty # \<Gamma> \<turnstile> ?R : Prop"
    by (rule infer_type_sound)
      (simp add: caie_term_defs caie_type_defs lookup_def eval_nat_numeral)
  have conjPhiE_type: "Ind # caie_prop_ty # \<Gamma> \<turnstile> ?ConjPhiE : Prop"
    using Phi_type E_type by auto
  have closure_uncurried: "Ind # caie_prop_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp ?Hax_shift2 (Imp ?ConjPhiE ?R)"
    using P2_type conjPhiE_type R_type closure
    by (rule CEV_uncurry_conj)
  have conj_to_R_type: "Ind # caie_prop_ty # \<Gamma> \<turnstile>
      Imp ?ConjPhiE ?R : Prop"
    using conjPhiE_type R_type by auto
  have inner_curried_type: "Ind # caie_prop_ty # \<Gamma> \<turnstile>
      Imp ?Phi_inner ?Body : Prop"
    using Phi_type E_type R_type by auto
  have uncurry_inner: "Ind # caie_prop_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp (Imp ?ConjPhiE ?R) (Imp ?Phi_inner ?Body)"
    using Phi_type E_type R_type by (rule CEV_uncurry_conj_imp)
  have P2_to_inner: "Ind # caie_prop_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp ?Hax_shift2 (Imp ?Phi_inner ?Body)"
    using P2_type conj_to_R_type inner_curried_type
      closure_uncurried uncurry_inner
    by (rule CEV_imp_trans)
  have body_type: "Ind # caie_prop_ty # \<Gamma> \<turnstile> ?Body : Prop"
    using E_type R_type by auto
  have combined_shifted: "Ind # caie_prop_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp (shift ?Combined) ?Body"
  proof -
    have combined_shift: "shift ?Combined = Conj ?Hax_shift2 ?Phi_inner"
      by (rule shift_caie_Thm36_combined_antecedent)
    have curried: "Ind # caie_prop_ty # \<Gamma> \<turnstile>\<^sub>CEV
        Imp (Conj ?Hax_shift2 ?Phi_inner) ?Body"
      using P2_type Phi_type body_type P2_to_inner
      by (rule CEV_curry_conj)
    then show ?thesis
      by (simp only: combined_shift)
  qed
  have P1_type: "caie_prop_ty # \<Gamma> \<turnstile> ?Hax_shift : Prop"
    using typed_caie_haecceity_up_extensionality_principle
    by (rule weakening_front)
  have Phi0_type: "caie_prop_ty # \<Gamma> \<turnstile> ?Phi_outer : Prop"
    by (rule infer_type_sound)
      (simp add: caie_term_defs caie_type_defs lookup_def eval_nat_numeral)
  have combined_type: "caie_prop_ty # \<Gamma> \<turnstile> ?Combined : Prop"
    using P1_type Phi0_type by auto
  have gen_x: "caie_prop_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp ?Combined ?ForallX"
    using combined_type body_type combined_shifted
    by (rule CEV_proves.Gen)
  have ForallX_type: "caie_prop_ty # \<Gamma> \<turnstile> ?ForallX : Prop"
    by (rule infer_type_sound)
      (simp add: caie_term_defs caie_type_defs lookup_def eval_nat_numeral)
  have outer_curried: "caie_prop_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp ?Hax_shift ?OuterBody"
    using P1_type Phi0_type ForallX_type gen_x
    by (rule CEV_uncurry_conj)
  have P0_type: "\<Gamma> \<turnstile> ?Hax : Prop"
    by (rule typed_caie_haecceity_up_extensionality_principle)
  have OuterBody_type: "caie_prop_ty # \<Gamma> \<turnstile> ?OuterBody : Prop"
    using Phi0_type ForallX_type by auto
  have gen_P: "\<Gamma> \<turnstile>\<^sub>CEV
      Imp ?Hax (Forall caie_prop_ty ?OuterBody)"
    using P0_type OuterBody_type outer_curried
    by (rule CEV_proves.Gen)
  then show ?thesis
    by (simp add: caie_Thm36_def)
qed


subsection \<open>Appendix C Theorem 32 from the axiom package\<close>

lemma beta_eta_caie_Thm32_expanded:
  "beta_eta_equiv \<Gamma> Prop caie_Thm32 caie_name_expanded_down_phae_principle"
proof -
  have left_type: "\<Gamma> \<turnstile> caie_Thm32 : Prop"
    by (rule typed_caie_Thm32)
  have right_type: "\<Gamma> \<turnstile> caie_name_expanded_down_phae_principle : Prop"
    by (rule typed_caie_name_expanded_down_phae_principle)
  have down_step: "compatible_step beta_contract
      (App caie_down_op (Var 0))
      (Lam Ind (App (Var 1) (caie_heq (Var 0))))"
  proof -
    have "compatible_step beta_contract
        (App caie_down_op (Var 0))
        (subst0 (Var 0) (Lam Ind (App (Var 1) (caie_heq (Var 0)))))"
      unfolding caie_down_op_def
      by (intro compatible_step.root beta_contract.beta)
    then show ?thesis
      by (simp add: subst0_def)
  qed
  have step: "compatible_step beta_contract
      caie_Thm32 caie_name_expanded_down_phae_principle"
    unfolding caie_Thm32_def caie_name_expanded_down_phae_principle_def
    by (intro compatible_step.Forall_body compatible_step.Imp_right
        compatible_step.App_right down_step)
  show ?thesis
    using left_type right_type step by (rule beta_eta_equiv.Beta)
qed

lemma CEV_caie_Thm32_expanded:
  "\<Gamma> \<turnstile>\<^sub>CEV (caie_Thm32 \<longleftrightarrow>\<^sub>o caie_name_expanded_down_phae_principle)"
  using beta_eta_caie_Thm32_expanded by (rule CEV_beta_eta_equiv)

lemma caie_CEV_derivable_Thm32_expanded_bridge:
  "caie_CEV_derivable \<Gamma> \<Delta>
    (caie_Thm32 \<longleftrightarrow>\<^sub>o caie_name_expanded_down_phae_principle)"
  using CEV_caie_Thm32_expanded by (rule caie_CEV_derivable_of_theorem)

lemma CEV_caie_Thm32_of_expanded:
  "\<Gamma> \<turnstile>\<^sub>CEV Imp caie_name_expanded_down_phae_principle caie_Thm32"
proof -
  have thm32_type: "\<Gamma> \<turnstile> caie_Thm32 : Prop"
    by (rule typed_caie_Thm32)
  have expanded_type: "\<Gamma> \<turnstile> caie_name_expanded_down_phae_principle : Prop"
    by (rule typed_caie_name_expanded_down_phae_principle)
  have bicond: "\<Gamma> \<turnstile>\<^sub>CEV
      (caie_Thm32 \<longleftrightarrow>\<^sub>o caie_name_expanded_down_phae_principle)"
    by (rule CEV_caie_Thm32_expanded)
  show ?thesis
    using thm32_type expanded_type bicond by (rule CEV_beta_right_imp)
qed

lemma caie_CEV_derivable_name_expanded_down_phae_from_axiom_package:
  "caie_CEV_derivable \<Gamma> caie_appendix_C_axiom_package
    caie_name_expanded_down_phae_principle"
proof -
  have components_member:
      "caie_name_expanded_down_phae_components_principle \<in>
        set caie_appendix_C_axiom_package"
    by (simp add: caie_appendix_C_axiom_package_def
        caie_name_haecceity_principles_def)
  have d_components: "caie_CEV_derivable \<Gamma> caie_appendix_C_axiom_package
      caie_name_expanded_down_phae_components_principle"
    using components_member by (rule caie_CEV_derivable_appendix_C_axiom)
  have d_components_to_expanded:
      "caie_CEV_derivable \<Gamma> caie_appendix_C_axiom_package
        (Imp caie_name_expanded_down_phae_components_principle
          caie_name_expanded_down_phae_principle)"
    using CEV_caie_name_expanded_down_phae_from_components
    by (rule caie_CEV_derivable_of_theorem)
  show ?thesis
    using d_components d_components_to_expanded
    by (rule caie_CEV_derivable.caie_MP)
qed

lemma caie_CEV_derivable_Thm32_from_axiom_package:
  "caie_CEV_derivable \<Gamma> caie_appendix_C_axiom_package caie_Thm32"
proof -
  have d_expanded: "caie_CEV_derivable \<Gamma> caie_appendix_C_axiom_package
      caie_name_expanded_down_phae_principle"
    by (rule caie_CEV_derivable_name_expanded_down_phae_from_axiom_package)
  have thm32_type: "\<Gamma> \<turnstile> caie_Thm32 : Prop"
    by (rule typed_caie_Thm32)
  have expanded_type: "\<Gamma> \<turnstile> caie_name_expanded_down_phae_principle : Prop"
    by (rule typed_caie_name_expanded_down_phae_principle)
  have d_bridge: "caie_CEV_derivable \<Gamma> caie_appendix_C_axiom_package
      (caie_Thm32 \<longleftrightarrow>\<^sub>o caie_name_expanded_down_phae_principle)"
    by (rule caie_CEV_derivable_Thm32_expanded_bridge)
  show ?thesis
    using thm32_type expanded_type d_bridge d_expanded
    by (rule caie_CEV_derivable_bicond_right)
qed

lemma caie_appendix_C_first_residual_target_from_axiom_package:
  "caie_CEV_derivable \<Gamma> caie_appendix_C_axiom_package caie_Thm32"
  by (rule caie_CEV_derivable_Thm32_from_axiom_package)


subsection \<open>Appendix C Theorem 33 from the axiom package\<close>

lemma caie_CEV_derivable_Thm33_component_principles_from_axiom_package:
  "caie_CEV_derivable \<Gamma> caie_appendix_C_axiom_package
    caie_Thm33_component_principles"
proof -
  have mc_member:
      "caie_phae_up_MC_principle \<in> set caie_appendix_C_axiom_package"
    by (simp add: caie_appendix_C_axiom_package_def
        caie_name_haecceity_principles_def)
  have ac_member:
      "caie_phae_up_AC_principle \<in> set caie_appendix_C_axiom_package"
    by (simp add: caie_appendix_C_axiom_package_def
        caie_name_haecceity_principles_def)
  have hp_member:
      "caie_phae_up_HP_principle \<in> set caie_appendix_C_axiom_package"
    by (simp add: caie_appendix_C_axiom_package_def
        caie_name_haecceity_principles_def)
  have nhp_member:
      "caie_phae_up_NHP_principle \<in> set caie_appendix_C_axiom_package"
    by (simp add: caie_appendix_C_axiom_package_def
        caie_name_haecceity_principles_def)
  have acf_member:
      "caie_phae_up_ACF_principle \<in> set caie_appendix_C_axiom_package"
    by (simp add: caie_appendix_C_axiom_package_def
        caie_name_haecceity_principles_def)
  have d_mc: "caie_CEV_derivable \<Gamma> caie_appendix_C_axiom_package
      caie_phae_up_MC_principle"
    using mc_member by (rule caie_CEV_derivable_appendix_C_axiom)
  have d_ac: "caie_CEV_derivable \<Gamma> caie_appendix_C_axiom_package
      caie_phae_up_AC_principle"
    using ac_member by (rule caie_CEV_derivable_appendix_C_axiom)
  have d_hp: "caie_CEV_derivable \<Gamma> caie_appendix_C_axiom_package
      caie_phae_up_HP_principle"
    using hp_member by (rule caie_CEV_derivable_appendix_C_axiom)
  have d_nhp: "caie_CEV_derivable \<Gamma> caie_appendix_C_axiom_package
      caie_phae_up_NHP_principle"
    using nhp_member by (rule caie_CEV_derivable_appendix_C_axiom)
  have d_acf: "caie_CEV_derivable \<Gamma> caie_appendix_C_axiom_package
      caie_phae_up_ACF_principle"
    using acf_member by (rule caie_CEV_derivable_appendix_C_axiom)
  have d_nhp_acf: "caie_CEV_derivable \<Gamma> caie_appendix_C_axiom_package
      (Conj caie_phae_up_NHP_principle caie_phae_up_ACF_principle)"
    using d_nhp d_acf by (rule caie_CEV_derivable_conj_intro)
  have d_hp_tail: "caie_CEV_derivable \<Gamma> caie_appendix_C_axiom_package
      (Conj caie_phae_up_HP_principle
        (Conj caie_phae_up_NHP_principle caie_phae_up_ACF_principle))"
    using d_hp d_nhp_acf by (rule caie_CEV_derivable_conj_intro)
  have d_ac_tail: "caie_CEV_derivable \<Gamma> caie_appendix_C_axiom_package
      (Conj caie_phae_up_AC_principle
        (Conj caie_phae_up_HP_principle
          (Conj caie_phae_up_NHP_principle caie_phae_up_ACF_principle)))"
    using d_ac d_hp_tail by (rule caie_CEV_derivable_conj_intro)
  have d_bundle: "caie_CEV_derivable \<Gamma> caie_appendix_C_axiom_package
      (Conj caie_phae_up_MC_principle
        (Conj caie_phae_up_AC_principle
          (Conj caie_phae_up_HP_principle
            (Conj caie_phae_up_NHP_principle caie_phae_up_ACF_principle))))"
    using d_mc d_ac_tail by (rule caie_CEV_derivable_conj_intro)
  then show ?thesis
    by (simp add: caie_Thm33_component_principles_def)
qed

lemma caie_CEV_derivable_Thm33_from_axiom_package:
  "caie_CEV_derivable \<Gamma> caie_appendix_C_axiom_package caie_Thm33"
proof -
  have d_components: "caie_CEV_derivable \<Gamma> caie_appendix_C_axiom_package
      caie_Thm33_component_principles"
    by (rule caie_CEV_derivable_Thm33_component_principles_from_axiom_package)
  have d_imp: "caie_CEV_derivable \<Gamma> caie_appendix_C_axiom_package
      (Imp caie_Thm33_component_principles caie_Thm33)"
    using CEV_caie_Thm33_from_component_principles
    by (rule caie_CEV_derivable_of_theorem)
  show ?thesis
    using d_components d_imp by (rule caie_CEV_derivable.caie_MP)
qed

lemma caie_appendix_C_second_residual_target_from_axiom_package:
  "caie_CEV_derivable \<Gamma> caie_appendix_C_axiom_package caie_Thm33"
  by (rule caie_CEV_derivable_Thm33_from_axiom_package)


subsection \<open>Appendix C Theorem 34 from the axiom package\<close>

lemma CEV_caie_phae_up_down_pointwise_instance:
  "Ind # caie_prop_ty # \<Gamma> \<turnstile>\<^sub>CEV
    Imp (shift (shift caie_phae_up_down_pointwise_principle))
      (Imp (caie_phae (Var 1))
        (App (Var 1) (Var 0)
          \<longleftrightarrow>\<^sub>o App ((Var 1\<^sup>\<up>\<^sub>c)\<^sup>\<down>\<^sub>c) (Var 0)))"
proof -
  let ?OuterBody =
    "Forall Ind
      (Imp (caie_phae (Var 1))
        (App (Var 1) (Var 0)
          \<longleftrightarrow>\<^sub>o App ((Var 1\<^sup>\<up>\<^sub>c)\<^sup>\<down>\<^sub>c) (Var 0)))"
  let ?LiftedOuterBody =
    "rename (lift_ren Suc) (rename (lift_ren Suc) ?OuterBody)"
  let ?ForallX =
    "Forall Ind
      (Imp (caie_phae (Var 2))
        (App (Var 2) (Var 0)
          \<longleftrightarrow>\<^sub>o App ((Var 2\<^sup>\<up>\<^sub>c)\<^sup>\<down>\<^sub>c) (Var 0)))"
  let ?Inst =
    "Imp (caie_phae (Var 1))
      (App (Var 1) (Var 0)
        \<longleftrightarrow>\<^sub>o App ((Var 1\<^sup>\<up>\<^sub>c)\<^sup>\<down>\<^sub>c) (Var 0))"
  have outer_body_type: "caie_prop_ty # \<Gamma> \<turnstile> ?OuterBody : Prop"
    by (rule infer_type_sound)
      (simp add: caie_term_defs caie_type_defs lookup_def)
  have lifted_outer_body_once_type:
      "caie_prop_ty # caie_prop_ty # \<Gamma> \<turnstile>
        rename (lift_ren Suc) ?OuterBody : Prop"
    using outer_body_type by (rule weakening_after_front)
  have lifted_outer_body_type:
      "caie_prop_ty # Ind # caie_prop_ty # \<Gamma> \<turnstile>
        ?LiftedOuterBody : Prop"
    using lifted_outer_body_once_type by (rule weakening_after_front)
  have var1_type: "Ind # caie_prop_ty # \<Gamma> \<turnstile> Var 1 : caie_prop_ty"
    by simp
  have outer_raw: "Ind # caie_prop_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp (Forall caie_prop_ty ?LiftedOuterBody)
        (subst0 (Var 1) ?LiftedOuterBody)"
    using lifted_outer_body_type var1_type by (rule CEV_forall_inst)
  have outer_ui: "Ind # caie_prop_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp (shift (shift caie_phae_up_down_pointwise_principle))
        ?ForallX"
    using outer_raw
    by (simp add: caie_phae_up_down_pointwise_principle_def
      caie_term_defs caie_type_defs shift_def subst0_def eval_nat_numeral)
  have inner_body_type: "Ind # Ind # caie_prop_ty # \<Gamma> \<turnstile>
      (Imp (caie_phae (Var 2))
        (App (Var 2) (Var 0)
          \<longleftrightarrow>\<^sub>o App ((Var 2\<^sup>\<up>\<^sub>c)\<^sup>\<down>\<^sub>c) (Var 0))) : Prop"
    by (rule infer_type_sound)
      (simp add: caie_term_defs caie_type_defs lookup_def)
  have var0_type: "Ind # caie_prop_ty # \<Gamma> \<turnstile> Var 0 : Ind"
    by simp
  have inner_raw: "Ind # caie_prop_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp ?ForallX
        (subst0 (Var 0)
          (Imp (caie_phae (Var 2))
            (App (Var 2) (Var 0)
              \<longleftrightarrow>\<^sub>o App ((Var 2\<^sup>\<up>\<^sub>c)\<^sup>\<down>\<^sub>c) (Var 0))))"
    using inner_body_type var0_type by (rule CEV_forall_inst)
  have inner_ui: "Ind # caie_prop_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp ?ForallX ?Inst"
    using inner_raw
    by (simp add: caie_term_defs caie_type_defs subst0_def eval_nat_numeral)
  have shifted_principle_type:
      "Ind # caie_prop_ty # \<Gamma> \<turnstile>
        shift (shift caie_phae_up_down_pointwise_principle) : Prop"
    using typed_caie_phae_up_down_pointwise_principle
    by (intro weakening_front)
  have forallX_type: "Ind # caie_prop_ty # \<Gamma> \<turnstile> ?ForallX : Prop"
    by (rule infer_type_sound)
      (simp add: caie_term_defs caie_type_defs lookup_def)
  have inst_type: "Ind # caie_prop_ty # \<Gamma> \<turnstile> ?Inst : Prop"
    by (rule infer_type_sound)
      (simp add: caie_term_defs caie_type_defs lookup_def)
  show ?thesis
    using shifted_principle_type forallX_type inst_type outer_ui inner_ui
    by (rule CEV_imp_trans)
qed

lemma CEV_caie_Thm34_from_up_down_pointwise:
  "\<Gamma> \<turnstile>\<^sub>CEV
    Imp caie_phae_up_down_pointwise_principle caie_Thm34"
proof -
  let ?Ax = "caie_phae_up_down_pointwise_principle"
  let ?Ax1 = "shift ?Ax"
  let ?Ax2 = "shift (shift ?Ax)"
  let ?Phi = "caie_phae (Var 0)"
  let ?Phi' = "caie_phae (Var 1)"
  let ?F = "Var 0"
  let ?G = "(Var 0\<^sup>\<up>\<^sub>c)\<^sup>\<down>\<^sub>c"
  let ?R = "Eq caie_prop_ty ?F ?G"
  let ?A = "Conj ?Ax1 ?Phi"
  let ?Point =
    "App (Var 1) (Var 0)
      \<longleftrightarrow>\<^sub>o App ((Var 1\<^sup>\<up>\<^sub>c)\<^sup>\<down>\<^sub>c) (Var 0)"
  let ?OuterBody = "Imp ?Phi ?R"
  have shift_A: "shift ?A = Conj ?Ax2 ?Phi'"
    by (simp add: shift_def)
  have Ax2_type: "Ind # caie_prop_ty # \<Gamma> \<turnstile> ?Ax2 : Prop"
    using typed_caie_phae_up_down_pointwise_principle
    by (intro weakening_front)
  have Phi'_type: "Ind # caie_prop_ty # \<Gamma> \<turnstile> ?Phi' : Prop"
    by (rule infer_type_sound)
      (simp add: caie_term_defs caie_type_defs lookup_def eval_nat_numeral)
  have Point_type: "Ind # caie_prop_ty # \<Gamma> \<turnstile> ?Point : Prop"
    by (rule infer_type_sound)
      (simp add: caie_term_defs caie_type_defs lookup_def eval_nat_numeral)
  have pointwise: "Ind # caie_prop_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp ?Ax2 (Imp ?Phi' ?Point)"
    by (rule CEV_caie_phae_up_down_pointwise_instance)
  have contextual_premise: "Ind # caie_prop_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp (shift ?A)
        (App (shift ?F) (Var 0) \<longleftrightarrow>\<^sub>o App (shift ?G) (Var 0))"
  proof -
    have grouped: "Ind # caie_prop_ty # \<Gamma> \<turnstile>\<^sub>CEV
        Imp (Conj ?Ax2 ?Phi') ?Point"
      using Ax2_type Phi'_type Point_type pointwise by (rule CEV_curry_conj)
    then show ?thesis
      by (simp add: shift_A shift_def)
  qed
  have Ax1_type: "caie_prop_ty # \<Gamma> \<turnstile> ?Ax1 : Prop"
    using typed_caie_phae_up_down_pointwise_principle
    by (rule weakening_front)
  have Phi_type: "caie_prop_ty # \<Gamma> \<turnstile> ?Phi : Prop"
    by (rule infer_type_sound)
      (simp add: caie_term_defs caie_type_defs lookup_def eval_nat_numeral)
  have A_type: "caie_prop_ty # \<Gamma> \<turnstile> ?A : Prop"
    using Ax1_type Phi_type by auto
  have F_type: "caie_prop_ty # \<Gamma> \<turnstile> ?F : caie_prop_ty"
    by simp
  have G_type: "caie_prop_ty # \<Gamma> \<turnstile> ?G : caie_prop_ty"
    using F_type by (intro typed_caie_down typed_caie_up)
  have F_arrow_type: "caie_prop_ty # \<Gamma> \<turnstile> ?F : Ind \<rightarrow>\<^sub>o Prop"
    using F_type by (simp add: caie_prop_ty_def pred_ty_def)
  have G_arrow_type: "caie_prop_ty # \<Gamma> \<turnstile> ?G : Ind \<rightarrow>\<^sub>o Prop"
    using G_type by (simp add: caie_prop_ty_def pred_ty_def)
  have closure_raw: "caie_prop_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp ?A (Eq (Ind \<rightarrow>\<^sub>o Prop) ?F ?G)"
    using A_type F_arrow_type G_arrow_type contextual_premise
    by (rule CEV_contextual_unary_equivalence[where \<sigma>=Ind])
  have closure: "caie_prop_ty # \<Gamma> \<turnstile>\<^sub>CEV Imp ?A ?R"
    using closure_raw by (simp add: caie_prop_ty_def pred_ty_def)
  have R_type: "caie_prop_ty # \<Gamma> \<turnstile> ?R : Prop"
    using F_type G_type by auto
  have outer: "caie_prop_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp ?Ax1 ?OuterBody"
    using Ax1_type Phi_type R_type closure by (rule CEV_uncurry_conj)
  have Ax_type: "\<Gamma> \<turnstile> ?Ax : Prop"
    by (rule typed_caie_phae_up_down_pointwise_principle)
  have OuterBody_type: "caie_prop_ty # \<Gamma> \<turnstile> ?OuterBody : Prop"
    using Phi_type R_type by auto
  have gen: "\<Gamma> \<turnstile>\<^sub>CEV
      Imp ?Ax (Forall caie_prop_ty ?OuterBody)"
    using Ax_type OuterBody_type outer by (rule CEV_proves.Gen)
  then show ?thesis
    by (simp add: caie_Thm34_def)
qed

lemma caie_CEV_derivable_Thm34_from_axiom_package:
  "caie_CEV_derivable \<Gamma> caie_appendix_C_axiom_package caie_Thm34"
proof -
  have member:
      "caie_phae_up_down_pointwise_principle \<in>
        set caie_appendix_C_axiom_package"
    by (simp add: caie_appendix_C_axiom_package_def
        caie_name_haecceity_principles_def)
  have d_ax: "caie_CEV_derivable \<Gamma> caie_appendix_C_axiom_package
      caie_phae_up_down_pointwise_principle"
    using member by (rule caie_CEV_derivable_appendix_C_axiom)
  have d_imp: "caie_CEV_derivable \<Gamma> caie_appendix_C_axiom_package
      (Imp caie_phae_up_down_pointwise_principle caie_Thm34)"
    using CEV_caie_Thm34_from_up_down_pointwise
    by (rule caie_CEV_derivable_of_theorem)
  show ?thesis
    using d_ax d_imp by (rule caie_CEV_derivable.caie_MP)
qed

lemma caie_appendix_C_fourth_residual_target_from_axiom_package:
  "caie_CEV_derivable \<Gamma> caie_appendix_C_axiom_package caie_Thm34"
  by (rule caie_CEV_derivable_Thm34_from_axiom_package)


subsection \<open>Appendix C Theorem 35 from the axiom package\<close>

lemma CEV_caie_name_down_up_pointwise_instance:
  "caie_prop_ty # caie_classifier_ty # \<Gamma> \<turnstile>\<^sub>CEV
    Imp (shift (shift caie_name_down_up_pointwise_principle))
      (Imp (caie_Name (Var 1))
        (App (Var 1) (Var 0)
          \<longleftrightarrow>\<^sub>o App ((Var 1\<^sup>\<down>\<^sub>c)\<^sup>\<up>\<^sub>c) (Var 0)))"
proof -
  let ?OuterBody =
    "Forall caie_prop_ty
      (Imp (caie_Name (Var 1))
        (App (Var 1) (Var 0)
          \<longleftrightarrow>\<^sub>o App ((Var 1\<^sup>\<down>\<^sub>c)\<^sup>\<up>\<^sub>c) (Var 0)))"
  let ?LiftedOuterBody =
    "rename (lift_ren Suc) (rename (lift_ren Suc) ?OuterBody)"
  let ?ForallP =
    "Forall caie_prop_ty
      (Imp (caie_Name (Var 2))
        (App (Var 2) (Var 0)
          \<longleftrightarrow>\<^sub>o App ((Var 2\<^sup>\<down>\<^sub>c)\<^sup>\<up>\<^sub>c) (Var 0)))"
  let ?Inst =
    "Imp (caie_Name (Var 1))
      (App (Var 1) (Var 0)
        \<longleftrightarrow>\<^sub>o App ((Var 1\<^sup>\<down>\<^sub>c)\<^sup>\<up>\<^sub>c) (Var 0))"
  have outer_body_type: "caie_classifier_ty # \<Gamma> \<turnstile> ?OuterBody : Prop"
    by (rule infer_type_sound)
      (simp add: caie_term_defs caie_type_defs lookup_def)
  have lifted_outer_body_once_type:
      "caie_classifier_ty # caie_classifier_ty # \<Gamma> \<turnstile>
        rename (lift_ren Suc) ?OuterBody : Prop"
    using outer_body_type by (rule weakening_after_front)
  have lifted_outer_body_type:
      "caie_classifier_ty # caie_prop_ty # caie_classifier_ty # \<Gamma> \<turnstile>
        ?LiftedOuterBody : Prop"
    using lifted_outer_body_once_type by (rule weakening_after_front)
  have var1_type:
      "caie_prop_ty # caie_classifier_ty # \<Gamma> \<turnstile>
        Var 1 : caie_classifier_ty"
    by simp
  have outer_raw: "caie_prop_ty # caie_classifier_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp (Forall caie_classifier_ty ?LiftedOuterBody)
        (subst0 (Var 1) ?LiftedOuterBody)"
    using lifted_outer_body_type var1_type by (rule CEV_forall_inst)
  have outer_ui: "caie_prop_ty # caie_classifier_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp (shift (shift caie_name_down_up_pointwise_principle))
        ?ForallP"
    using outer_raw
    by (simp add: caie_name_down_up_pointwise_principle_def
      caie_term_defs caie_type_defs shift_def subst0_def eval_nat_numeral)
  have inner_body_type:
      "caie_prop_ty # caie_prop_ty # caie_classifier_ty # \<Gamma> \<turnstile>
        (Imp (caie_Name (Var 2))
          (App (Var 2) (Var 0)
            \<longleftrightarrow>\<^sub>o App ((Var 2\<^sup>\<down>\<^sub>c)\<^sup>\<up>\<^sub>c) (Var 0))) : Prop"
    by (rule infer_type_sound)
      (simp add: caie_term_defs caie_type_defs lookup_def)
  have var0_type:
      "caie_prop_ty # caie_classifier_ty # \<Gamma> \<turnstile> Var 0 : caie_prop_ty"
    by simp
  have inner_raw: "caie_prop_ty # caie_classifier_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp ?ForallP
        (subst0 (Var 0)
          (Imp (caie_Name (Var 2))
            (App (Var 2) (Var 0)
              \<longleftrightarrow>\<^sub>o App ((Var 2\<^sup>\<down>\<^sub>c)\<^sup>\<up>\<^sub>c) (Var 0))))"
    using inner_body_type var0_type by (rule CEV_forall_inst)
  have inner_ui: "caie_prop_ty # caie_classifier_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp ?ForallP ?Inst"
    using inner_raw
    by (simp add: caie_term_defs caie_type_defs subst0_def eval_nat_numeral)
  have shifted_principle_type:
      "caie_prop_ty # caie_classifier_ty # \<Gamma> \<turnstile>
        shift (shift caie_name_down_up_pointwise_principle) : Prop"
    using typed_caie_name_down_up_pointwise_principle
    by (intro weakening_front)
  have forallP_type:
      "caie_prop_ty # caie_classifier_ty # \<Gamma> \<turnstile> ?ForallP : Prop"
    by (rule infer_type_sound)
      (simp add: caie_term_defs caie_type_defs lookup_def)
  have inst_type:
      "caie_prop_ty # caie_classifier_ty # \<Gamma> \<turnstile> ?Inst : Prop"
    by (rule infer_type_sound)
      (simp add: caie_term_defs caie_type_defs lookup_def)
  show ?thesis
    using shifted_principle_type forallP_type inst_type outer_ui inner_ui
    by (rule CEV_imp_trans)
qed

lemma CEV_caie_Thm35_from_down_up_pointwise:
  "\<Gamma> \<turnstile>\<^sub>CEV
    Imp caie_name_down_up_pointwise_principle caie_Thm35"
proof -
  let ?Ax = "caie_name_down_up_pointwise_principle"
  let ?Ax1 = "shift ?Ax"
  let ?Ax2 = "shift (shift ?Ax)"
  let ?Name = "caie_Name (Var 0)"
  let ?Name' = "caie_Name (Var 1)"
  let ?F = "Var 0"
  let ?G = "(Var 0\<^sup>\<down>\<^sub>c)\<^sup>\<up>\<^sub>c"
  let ?R = "Eq caie_classifier_ty ?F ?G"
  let ?A = "Conj ?Ax1 ?Name"
  let ?Point =
    "App (Var 1) (Var 0)
      \<longleftrightarrow>\<^sub>o App ((Var 1\<^sup>\<down>\<^sub>c)\<^sup>\<up>\<^sub>c) (Var 0)"
  let ?OuterBody = "Imp ?Name ?R"
  have shift_A: "shift ?A = Conj ?Ax2 ?Name'"
    by (simp add: shift_def)
  have Ax2_type: "caie_prop_ty # caie_classifier_ty # \<Gamma> \<turnstile> ?Ax2 : Prop"
    using typed_caie_name_down_up_pointwise_principle
    by (intro weakening_front)
  have Name'_type:
      "caie_prop_ty # caie_classifier_ty # \<Gamma> \<turnstile> ?Name' : Prop"
    by (rule infer_type_sound)
      (simp add: caie_term_defs caie_type_defs lookup_def eval_nat_numeral)
  have Point_type:
      "caie_prop_ty # caie_classifier_ty # \<Gamma> \<turnstile> ?Point : Prop"
    by (rule infer_type_sound)
      (simp add: caie_term_defs caie_type_defs lookup_def eval_nat_numeral)
  have pointwise: "caie_prop_ty # caie_classifier_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp ?Ax2 (Imp ?Name' ?Point)"
    by (rule CEV_caie_name_down_up_pointwise_instance)
  have contextual_premise: "caie_prop_ty # caie_classifier_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp (shift ?A)
        (App (shift ?F) (Var 0) \<longleftrightarrow>\<^sub>o App (shift ?G) (Var 0))"
  proof -
    have grouped: "caie_prop_ty # caie_classifier_ty # \<Gamma> \<turnstile>\<^sub>CEV
        Imp (Conj ?Ax2 ?Name') ?Point"
      using Ax2_type Name'_type Point_type pointwise by (rule CEV_curry_conj)
    then show ?thesis
      by (simp add: shift_A shift_def)
  qed
  have Ax1_type: "caie_classifier_ty # \<Gamma> \<turnstile> ?Ax1 : Prop"
    using typed_caie_name_down_up_pointwise_principle
    by (rule weakening_front)
  have Name_type: "caie_classifier_ty # \<Gamma> \<turnstile> ?Name : Prop"
    by (rule infer_type_sound)
      (simp add: caie_term_defs caie_type_defs lookup_def eval_nat_numeral)
  have A_type: "caie_classifier_ty # \<Gamma> \<turnstile> ?A : Prop"
    using Ax1_type Name_type by auto
  have F_type: "caie_classifier_ty # \<Gamma> \<turnstile> ?F : caie_classifier_ty"
    by simp
  have G_type: "caie_classifier_ty # \<Gamma> \<turnstile> ?G : caie_classifier_ty"
    using F_type by (intro typed_caie_up typed_caie_down)
  have F_arrow_type:
      "caie_classifier_ty # \<Gamma> \<turnstile> ?F : caie_prop_ty \<rightarrow>\<^sub>o Prop"
    using F_type by (simp add: caie_classifier_ty_def)
  have G_arrow_type:
      "caie_classifier_ty # \<Gamma> \<turnstile> ?G : caie_prop_ty \<rightarrow>\<^sub>o Prop"
    using G_type by (simp add: caie_classifier_ty_def)
  have closure_raw: "caie_classifier_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp ?A (Eq (caie_prop_ty \<rightarrow>\<^sub>o Prop) ?F ?G)"
    using A_type F_arrow_type G_arrow_type contextual_premise
    by (rule CEV_contextual_unary_equivalence[where \<sigma>=caie_prop_ty])
  have closure: "caie_classifier_ty # \<Gamma> \<turnstile>\<^sub>CEV Imp ?A ?R"
    using closure_raw by (simp add: caie_classifier_ty_def)
  have R_type: "caie_classifier_ty # \<Gamma> \<turnstile> ?R : Prop"
    using F_type G_type by auto
  have outer: "caie_classifier_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp ?Ax1 ?OuterBody"
    using Ax1_type Name_type R_type closure by (rule CEV_uncurry_conj)
  have Ax_type: "\<Gamma> \<turnstile> ?Ax : Prop"
    by (rule typed_caie_name_down_up_pointwise_principle)
  have OuterBody_type: "caie_classifier_ty # \<Gamma> \<turnstile> ?OuterBody : Prop"
    using Name_type R_type by auto
  have gen: "\<Gamma> \<turnstile>\<^sub>CEV
      Imp ?Ax (Forall caie_classifier_ty ?OuterBody)"
    using Ax_type OuterBody_type outer by (rule CEV_proves.Gen)
  then show ?thesis
    by (simp add: caie_Thm35_def)
qed

lemma caie_CEV_derivable_Thm35_from_axiom_package:
  "caie_CEV_derivable \<Gamma> caie_appendix_C_axiom_package caie_Thm35"
proof -
  have member:
      "caie_name_down_up_pointwise_principle \<in>
        set caie_appendix_C_axiom_package"
    by (simp add: caie_appendix_C_axiom_package_def
        caie_name_haecceity_principles_def)
  have d_ax: "caie_CEV_derivable \<Gamma> caie_appendix_C_axiom_package
      caie_name_down_up_pointwise_principle"
    using member by (rule caie_CEV_derivable_appendix_C_axiom)
  have d_imp: "caie_CEV_derivable \<Gamma> caie_appendix_C_axiom_package
      (Imp caie_name_down_up_pointwise_principle caie_Thm35)"
    using CEV_caie_Thm35_from_down_up_pointwise
    by (rule caie_CEV_derivable_of_theorem)
  show ?thesis
    using d_ax d_imp by (rule caie_CEV_derivable.caie_MP)
qed

lemma caie_appendix_C_fifth_residual_target_from_axiom_package:
  "caie_CEV_derivable \<Gamma> caie_appendix_C_axiom_package caie_Thm35"
  by (rule caie_CEV_derivable_Thm35_from_axiom_package)


subsection \<open>Appendix C Theorem 36 from the axiom package\<close>

lemma caie_CEV_derivable_Thm36_from_axiom_package:
  "caie_CEV_derivable \<Gamma> caie_appendix_C_axiom_package caie_Thm36"
proof -
  have haecceity_up_member:
      "caie_haecceity_up_extensionality_principle \<in>
        set caie_appendix_C_axiom_package"
    by (simp add: caie_appendix_C_axiom_package_def
        caie_name_haecceity_principles_def)
  have d_haecceity_up:
      "caie_CEV_derivable \<Gamma> caie_appendix_C_axiom_package
        caie_haecceity_up_extensionality_principle"
    using haecceity_up_member by (rule caie_CEV_derivable_appendix_C_axiom)
  have d_imp: "caie_CEV_derivable \<Gamma> caie_appendix_C_axiom_package
      (Imp caie_haecceity_up_extensionality_principle caie_Thm36)"
    using CEV_caie_Thm36_from_haecceity_up_extensionality
    by (rule caie_CEV_derivable_of_theorem)
  show ?thesis
    using d_haecceity_up d_imp by (rule caie_CEV_derivable.caie_MP)
qed

lemma caie_appendix_C_third_residual_target_from_axiom_package:
  "caie_CEV_derivable \<Gamma> caie_appendix_C_axiom_package caie_Thm36"
  by (rule caie_CEV_derivable_Thm36_from_axiom_package)


subsection \<open>Appendix C Theorem 37 from the axiom package\<close>

lemma CEV_caie_phae_up_hae_witness_instance:
  "Ind # caie_prop_ty # \<Gamma> \<turnstile>\<^sub>CEV
    Imp (shift (shift caie_phae_up_hae_witness_principle))
      (Imp (caie_phae (Var 1))
        (Imp (caie_up_body (Var 1) (caie_heq (Var 0)))
          (caie_hae (Var 1))))"
proof -
  let ?OuterBody =
    "Forall Ind
      (Imp (caie_phae (Var 1))
        (Imp (caie_up_body (Var 1) (caie_heq (Var 0)))
          (caie_hae (Var 1))))"
  let ?LiftedOuterBody =
    "rename (lift_ren Suc) (rename (lift_ren Suc) ?OuterBody)"
  let ?ForallX =
    "Forall Ind
      (Imp (caie_phae (Var 2))
        (Imp (caie_up_body (Var 2) (caie_heq (Var 0)))
          (caie_hae (Var 2))))"
  let ?Inst =
    "Imp (caie_phae (Var 1))
      (Imp (caie_up_body (Var 1) (caie_heq (Var 0)))
        (caie_hae (Var 1)))"
  have outer_body_type: "caie_prop_ty # \<Gamma> \<turnstile> ?OuterBody : Prop"
    by (rule infer_type_sound)
      (simp add: caie_term_defs caie_type_defs lookup_def)
  have lifted_outer_body_once_type:
      "caie_prop_ty # caie_prop_ty # \<Gamma> \<turnstile>
        rename (lift_ren Suc) ?OuterBody : Prop"
    using outer_body_type by (rule weakening_after_front)
  have lifted_outer_body_type:
      "caie_prop_ty # Ind # caie_prop_ty # \<Gamma> \<turnstile>
        ?LiftedOuterBody : Prop"
    using lifted_outer_body_once_type by (rule weakening_after_front)
  have var1_type: "Ind # caie_prop_ty # \<Gamma> \<turnstile> Var 1 : caie_prop_ty"
    by simp
  have outer_raw: "Ind # caie_prop_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp (Forall caie_prop_ty ?LiftedOuterBody)
        (subst0 (Var 1) ?LiftedOuterBody)"
    using lifted_outer_body_type var1_type by (rule CEV_forall_inst)
  have outer_ui: "Ind # caie_prop_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp (shift (shift caie_phae_up_hae_witness_principle))
        ?ForallX"
    using outer_raw
    by (simp add: caie_phae_up_hae_witness_principle_def
      caie_term_defs caie_type_defs shift_def subst0_def eval_nat_numeral)
  have inner_body_type: "Ind # Ind # caie_prop_ty # \<Gamma> \<turnstile>
      (Imp (caie_phae (Var 2))
        (Imp (caie_up_body (Var 2) (caie_heq (Var 0)))
          (caie_hae (Var 2)))) : Prop"
    by (rule infer_type_sound)
      (simp add: caie_term_defs caie_type_defs lookup_def)
  have var0_type: "Ind # caie_prop_ty # \<Gamma> \<turnstile> Var 0 : Ind"
    by simp
  have inner_raw: "Ind # caie_prop_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp ?ForallX
        (subst0 (Var 0)
          (Imp (caie_phae (Var 2))
            (Imp (caie_up_body (Var 2) (caie_heq (Var 0)))
              (caie_hae (Var 2)))))"
    using inner_body_type var0_type by (rule CEV_forall_inst)
  have inner_ui: "Ind # caie_prop_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp ?ForallX ?Inst"
    using inner_raw
    by (simp add: caie_term_defs caie_type_defs subst0_def eval_nat_numeral)
  have shifted_principle_type:
      "Ind # caie_prop_ty # \<Gamma> \<turnstile>
        shift (shift caie_phae_up_hae_witness_principle) : Prop"
    using typed_caie_phae_up_hae_witness_principle
    by (intro weakening_front)
  have forallX_type: "Ind # caie_prop_ty # \<Gamma> \<turnstile> ?ForallX : Prop"
    by (rule infer_type_sound)
      (simp add: caie_term_defs caie_type_defs lookup_def)
  have inst_type: "Ind # caie_prop_ty # \<Gamma> \<turnstile> ?Inst : Prop"
    by (rule infer_type_sound)
      (simp add: caie_term_defs caie_type_defs lookup_def)
  show ?thesis
    using shifted_principle_type forallX_type inst_type outer_ui inner_ui
    by (rule CEV_imp_trans)
qed

lemma CEV_caie_Thm37_from_up_hae_witness:
  "\<Gamma> \<turnstile>\<^sub>CEV
    Imp caie_phae_up_hae_witness_principle caie_Thm37"
proof -
  let ?Ax = "caie_phae_up_hae_witness_principle"
  let ?Ax1 = "shift ?Ax"
  let ?Ax2 = "shift (shift ?Ax)"
  let ?Phi = "caie_phae (Var 0)"
  let ?Hae = "caie_hae (Var 0)"
  let ?Ante = "Conj ?Phi (Neg ?Hae)"
  let ?A = "Conj ?Ax1 ?Ante"
  let ?Phi' = "caie_phae (Var 1)"
  let ?Hae' = "caie_hae (Var 1)"
  let ?R = "caie_heq (Var 0)"
  let ?Up = "App (Var 1\<^sup>\<up>\<^sub>c) ?R"
  let ?Body = "caie_up_body (Var 1) ?R"
  let ?NegUp = "Neg ?Up"
  let ?Combined = "Conj ?Ax2 (Conj ?Phi' (Neg ?Hae'))"
  let ?PointImp = "Imp ?Ax2 (Imp ?Phi' (Imp ?Body ?Hae'))"
  let ?UpToBody = "Imp ?Up ?Body"
  let ?ForallX = "Forall Ind ?NegUp"
  let ?OuterBody = "Imp ?Ante ?ForallX"
  have shift_A: "shift ?A = ?Combined"
    by (simp add: shift_def)
  have Ax2_type: "Ind # caie_prop_ty # \<Gamma> \<turnstile> ?Ax2 : Prop"
    using typed_caie_phae_up_hae_witness_principle
    by (intro weakening_front)
  have Phi'_type: "Ind # caie_prop_ty # \<Gamma> \<turnstile> ?Phi' : Prop"
    by (rule infer_type_sound)
      (simp add: caie_term_defs caie_type_defs lookup_def eval_nat_numeral)
  have Hae'_type: "Ind # caie_prop_ty # \<Gamma> \<turnstile> ?Hae' : Prop"
    by (rule infer_type_sound)
      (simp add: caie_term_defs caie_type_defs lookup_def eval_nat_numeral)
  have P_type: "Ind # caie_prop_ty # \<Gamma> \<turnstile> Var 1 : caie_prop_ty"
    by simp
  have x_type: "Ind # caie_prop_ty # \<Gamma> \<turnstile> Var 0 : Ind"
    by simp
  have R_type: "Ind # caie_prop_ty # \<Gamma> \<turnstile> ?R : caie_prop_ty"
    using x_type by (rule typed_caie_heq)
  have Up_type: "Ind # caie_prop_ty # \<Gamma> \<turnstile> ?Up : Prop"
    by (rule infer_type_sound)
      (simp add: caie_term_defs caie_type_defs lookup_def eval_nat_numeral)
  have Body_type: "Ind # caie_prop_ty # \<Gamma> \<turnstile> ?Body : Prop"
    using P_type R_type by (rule typed_caie_up_body)
  have NegUp_type: "Ind # caie_prop_ty # \<Gamma> \<turnstile> ?NegUp : Prop"
    using Up_type by auto
  have PointImp_type: "Ind # caie_prop_ty # \<Gamma> \<turnstile> ?PointImp : Prop"
    using Ax2_type Phi'_type Body_type Hae'_type by auto
  have UpToBody_type: "Ind # caie_prop_ty # \<Gamma> \<turnstile> ?UpToBody : Prop"
    using Up_type Body_type by auto
  have Combined_type: "Ind # caie_prop_ty # \<Gamma> \<turnstile> ?Combined : Prop"
    using Ax2_type Phi'_type Hae'_type by auto
  have pointwise: "Ind # caie_prop_ty # \<Gamma> \<turnstile>\<^sub>CEV ?PointImp"
    by (rule CEV_caie_phae_up_hae_witness_instance)
  have up_bridge: "Ind # caie_prop_ty # \<Gamma> \<turnstile>\<^sub>CEV
      (?Up \<longleftrightarrow>\<^sub>o ?Body)"
    using P_type R_type by (rule CEV_caie_up_apply)
  have up_to_body: "Ind # caie_prop_ty # \<Gamma> \<turnstile>\<^sub>CEV ?UpToBody"
    using Up_type Body_type up_bridge by (rule CEV_beta_left_imp)
  have contra_taut: "prop_tautology (Ind # caie_prop_ty # \<Gamma>)
      (Imp ?PointImp (Imp ?UpToBody (Imp ?Combined ?NegUp)))"
    unfolding prop_tautology_def
    using PointImp_type UpToBody_type Combined_type NegUp_type by auto
  have contra_step1: "Ind # caie_prop_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp ?UpToBody (Imp ?Combined ?NegUp)"
    using pointwise CEV_prop_tautology[OF contra_taut] by (rule CEV_proves.MP)
  have inner: "Ind # caie_prop_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp ?Combined ?NegUp"
    using up_to_body contra_step1 by (rule CEV_proves.MP)
  have inner_shifted: "Ind # caie_prop_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp (shift ?A) ?NegUp"
    using inner by (simp only: shift_A)
  have Ax1_type: "caie_prop_ty # \<Gamma> \<turnstile> ?Ax1 : Prop"
    using typed_caie_phae_up_hae_witness_principle
    by (rule weakening_front)
  have Phi_type: "caie_prop_ty # \<Gamma> \<turnstile> ?Phi : Prop"
    by (rule infer_type_sound)
      (simp add: caie_term_defs caie_type_defs lookup_def eval_nat_numeral)
  have Hae_type: "caie_prop_ty # \<Gamma> \<turnstile> ?Hae : Prop"
    by (rule infer_type_sound)
      (simp add: caie_term_defs caie_type_defs lookup_def eval_nat_numeral)
  have Ante_type: "caie_prop_ty # \<Gamma> \<turnstile> ?Ante : Prop"
    using Phi_type Hae_type by auto
  have A_type: "caie_prop_ty # \<Gamma> \<turnstile> ?A : Prop"
    using Ax1_type Ante_type by auto
  have inner_body_type: "Ind # caie_prop_ty # \<Gamma> \<turnstile> ?NegUp : Prop"
    by (rule NegUp_type)
  have inner_forall: "caie_prop_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp ?A ?ForallX"
    using A_type inner_body_type inner_shifted by (rule CEV_proves.Gen)
  have ForallX_type: "caie_prop_ty # \<Gamma> \<turnstile> ?ForallX : Prop"
    using inner_body_type by auto
  have outer: "caie_prop_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp ?Ax1 ?OuterBody"
    using Ax1_type Ante_type ForallX_type inner_forall
    by (rule CEV_uncurry_conj)
  have Ax_type: "\<Gamma> \<turnstile> ?Ax : Prop"
    by (rule typed_caie_phae_up_hae_witness_principle)
  have OuterBody_type: "caie_prop_ty # \<Gamma> \<turnstile> ?OuterBody : Prop"
    using Ante_type ForallX_type by auto
  have gen: "\<Gamma> \<turnstile>\<^sub>CEV
      Imp ?Ax (Forall caie_prop_ty ?OuterBody)"
    using Ax_type OuterBody_type outer by (rule CEV_proves.Gen)
  then show ?thesis
    by (simp add: caie_Thm37_def)
qed

lemma caie_CEV_derivable_Thm37_from_axiom_package:
  "caie_CEV_derivable \<Gamma> caie_appendix_C_axiom_package caie_Thm37"
proof -
  have member:
      "caie_phae_up_hae_witness_principle \<in>
        set caie_appendix_C_axiom_package"
    by (simp add: caie_appendix_C_axiom_package_def
        caie_name_haecceity_principles_def)
  have d_ax: "caie_CEV_derivable \<Gamma> caie_appendix_C_axiom_package
      caie_phae_up_hae_witness_principle"
    using member by (rule caie_CEV_derivable_appendix_C_axiom)
  have d_imp: "caie_CEV_derivable \<Gamma> caie_appendix_C_axiom_package
      (Imp caie_phae_up_hae_witness_principle caie_Thm37)"
    using CEV_caie_Thm37_from_up_hae_witness
    by (rule caie_CEV_derivable_of_theorem)
  show ?thesis
    using d_ax d_imp by (rule caie_CEV_derivable.caie_MP)
qed

lemma caie_appendix_C_sixth_residual_target_from_axiom_package:
  "caie_CEV_derivable \<Gamma> caie_appendix_C_axiom_package caie_Thm37"
  by (rule caie_CEV_derivable_Thm37_from_axiom_package)


subsection \<open>Appendix C Theorem 38 from the axiom package\<close>

lemma CEV_caie_wname_dsim_surrogacy_instance:
  "caie_classifier_ty # caie_classifier_ty # \<Gamma> \<turnstile>\<^sub>CEV
    Imp (shift (shift caie_wname_dsim_surrogacy_principle))
      (Imp (Conj (caie_WName (Var 1)) (caie_WName (Var 0)))
        (Eq caie_prop_ty ((Var 1)\<^sup>\<down>\<^sub>c) ((Var 0)\<^sup>\<down>\<^sub>c)
          \<longleftrightarrow>\<^sub>o
         \<box>\<^sub>o
           (Imp
             (Exists Ind
               (Disj
                 (Eq caie_classifier_ty (Var 2)
                   (Lam caie_prop_ty (App (Var 0) (Var 1))))
                 (Eq caie_classifier_ty (Var 1)
                   (Lam caie_prop_ty (App (Var 0) (Var 1))))))
             (Eq caie_classifier_ty (Var 1) (Var 0)))))"
proof -
  let ?OuterBody =
    "Forall caie_classifier_ty
      (Imp (Conj (caie_WName (Var 1)) (caie_WName (Var 0)))
        (Eq caie_prop_ty ((Var 1)\<^sup>\<down>\<^sub>c) ((Var 0)\<^sup>\<down>\<^sub>c)
          \<longleftrightarrow>\<^sub>o
         \<box>\<^sub>o
           (Imp
             (Exists Ind
               (Disj
                 (Eq caie_classifier_ty (Var 2)
                   (Lam caie_prop_ty (App (Var 0) (Var 1))))
                 (Eq caie_classifier_ty (Var 1)
                   (Lam caie_prop_ty (App (Var 0) (Var 1))))))
             (Eq caie_classifier_ty (Var 1) (Var 0)))))"
  let ?LiftedOuterBody =
    "rename (lift_ren Suc) (rename (lift_ren Suc) ?OuterBody)"
  let ?ForallZ =
    "Forall caie_classifier_ty
      (Imp (Conj (caie_WName (Var 2)) (caie_WName (Var 0)))
        (Eq caie_prop_ty ((Var 2)\<^sup>\<down>\<^sub>c) ((Var 0)\<^sup>\<down>\<^sub>c)
          \<longleftrightarrow>\<^sub>o
         \<box>\<^sub>o
           (Imp
             (Exists Ind
               (Disj
                 (Eq caie_classifier_ty (Var 3)
                   (Lam caie_prop_ty (App (Var 0) (Var 1))))
                 (Eq caie_classifier_ty (Var 1)
                   (Lam caie_prop_ty (App (Var 0) (Var 1))))))
             (Eq caie_classifier_ty (Var 2) (Var 0)))))"
  let ?Inst =
    "Imp (Conj (caie_WName (Var 1)) (caie_WName (Var 0)))
      (Eq caie_prop_ty ((Var 1)\<^sup>\<down>\<^sub>c) ((Var 0)\<^sup>\<down>\<^sub>c)
        \<longleftrightarrow>\<^sub>o
       \<box>\<^sub>o
         (Imp
           (Exists Ind
             (Disj
               (Eq caie_classifier_ty (Var 2)
                 (Lam caie_prop_ty (App (Var 0) (Var 1))))
               (Eq caie_classifier_ty (Var 1)
                 (Lam caie_prop_ty (App (Var 0) (Var 1))))))
           (Eq caie_classifier_ty (Var 1) (Var 0))))"
  have outer_body_type: "caie_classifier_ty # \<Gamma> \<turnstile> ?OuterBody : Prop"
    by (rule infer_type_sound)
      (simp add: caie_term_defs caie_type_defs lookup_def)
  have lifted_outer_body_once_type:
      "caie_classifier_ty # caie_classifier_ty # \<Gamma> \<turnstile>
        rename (lift_ren Suc) ?OuterBody : Prop"
    using outer_body_type by (rule weakening_after_front)
  have lifted_outer_body_type:
      "caie_classifier_ty # caie_classifier_ty # caie_classifier_ty # \<Gamma> \<turnstile>
        ?LiftedOuterBody : Prop"
    using lifted_outer_body_once_type by (rule weakening_after_front)
  have var1_type:
      "caie_classifier_ty # caie_classifier_ty # \<Gamma> \<turnstile>
        Var 1 : caie_classifier_ty"
    by simp
  have outer_raw: "caie_classifier_ty # caie_classifier_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp (Forall caie_classifier_ty ?LiftedOuterBody)
        (subst0 (Var 1) ?LiftedOuterBody)"
    using lifted_outer_body_type var1_type by (rule CEV_forall_inst)
  have outer_ui: "caie_classifier_ty # caie_classifier_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp (shift (shift caie_wname_dsim_surrogacy_principle))
        ?ForallZ"
    using outer_raw
    by (simp add: caie_wname_dsim_surrogacy_principle_def
      caie_term_defs caie_type_defs shift_def subst0_def eval_nat_numeral)
  have inner_body_type:
      "caie_classifier_ty # caie_classifier_ty # caie_classifier_ty # \<Gamma> \<turnstile>
        (Imp (Conj (caie_WName (Var 2)) (caie_WName (Var 0)))
          (Eq caie_prop_ty ((Var 2)\<^sup>\<down>\<^sub>c) ((Var 0)\<^sup>\<down>\<^sub>c)
            \<longleftrightarrow>\<^sub>o
           \<box>\<^sub>o
             (Imp
               (Exists Ind
                 (Disj
                   (Eq caie_classifier_ty (Var 3)
                     (Lam caie_prop_ty (App (Var 0) (Var 1))))
                   (Eq caie_classifier_ty (Var 1)
                     (Lam caie_prop_ty (App (Var 0) (Var 1))))))
               (Eq caie_classifier_ty (Var 2) (Var 0))))) : Prop"
    by (rule infer_type_sound)
      (simp add: caie_term_defs caie_type_defs lookup_def)
  have var0_type:
      "caie_classifier_ty # caie_classifier_ty # \<Gamma> \<turnstile>
        Var 0 : caie_classifier_ty"
    by simp
  have inner_raw: "caie_classifier_ty # caie_classifier_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp ?ForallZ
        (subst0 (Var 0)
          (Imp (Conj (caie_WName (Var 2)) (caie_WName (Var 0)))
            (Eq caie_prop_ty ((Var 2)\<^sup>\<down>\<^sub>c) ((Var 0)\<^sup>\<down>\<^sub>c)
              \<longleftrightarrow>\<^sub>o
             \<box>\<^sub>o
               (Imp
                 (Exists Ind
                   (Disj
                     (Eq caie_classifier_ty (Var 3)
                       (Lam caie_prop_ty (App (Var 0) (Var 1))))
                     (Eq caie_classifier_ty (Var 1)
                       (Lam caie_prop_ty (App (Var 0) (Var 1))))))
                 (Eq caie_classifier_ty (Var 2) (Var 0))))))"
    using inner_body_type var0_type by (rule CEV_forall_inst)
  have inner_ui: "caie_classifier_ty # caie_classifier_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp ?ForallZ ?Inst"
    using inner_raw
    by (simp add: caie_term_defs caie_type_defs subst0_def eval_nat_numeral)
  have shifted_principle_type:
      "caie_classifier_ty # caie_classifier_ty # \<Gamma> \<turnstile>
        shift (shift caie_wname_dsim_surrogacy_principle) : Prop"
    using typed_caie_wname_dsim_surrogacy_principle
    by (intro weakening_front)
  have forallZ_type:
      "caie_classifier_ty # caie_classifier_ty # \<Gamma> \<turnstile> ?ForallZ : Prop"
    by (rule infer_type_sound)
      (simp add: caie_term_defs caie_type_defs lookup_def)
  have inst_type:
      "caie_classifier_ty # caie_classifier_ty # \<Gamma> \<turnstile> ?Inst : Prop"
    by (rule infer_type_sound)
      (simp add: caie_term_defs caie_type_defs lookup_def)
  show ?thesis
    using shifted_principle_type forallZ_type inst_type outer_ui inner_ui
    by (rule CEV_imp_trans)
qed

lemma CEV_caie_Thm38_from_wname_dsim_surrogacy:
  "\<Gamma> \<turnstile>\<^sub>CEV
    Imp caie_wname_dsim_surrogacy_principle caie_Thm38"
proof -
  let ?Ax = "caie_wname_dsim_surrogacy_principle"
  let ?Ax1 = "shift ?Ax"
  let ?Ax2 = "shift (shift ?Ax)"
  let ?Ante = "Conj (caie_WName (Var 1)) (caie_WName (Var 0))"
  let ?Dsim = "Var 1 \<sim>\<^sub>\<down>c Var 0"
  let ?DownEq =
    "Eq caie_prop_ty ((Var 1)\<^sup>\<down>\<^sub>c) ((Var 0)\<^sup>\<down>\<^sub>c)"
  let ?BoxCond =
    "\<box>\<^sub>o
      (Imp
        (Exists Ind
          (Disj
            (Eq caie_classifier_ty (Var 2)
              (Lam caie_prop_ty (App (Var 0) (Var 1))))
            (Eq caie_classifier_ty (Var 1)
              (Lam caie_prop_ty (App (Var 0) (Var 1))))))
        (Eq caie_classifier_ty (Var 1) (Var 0)))"
  let ?DownBic = "?DownEq \<longleftrightarrow>\<^sub>o ?BoxCond"
  let ?OfficialBic = "?Dsim \<longleftrightarrow>\<^sub>o ?BoxCond"
  let ?InnerBody = "Imp ?Ante ?OfficialBic"
  have Ax2_type: "caie_classifier_ty # caie_classifier_ty # \<Gamma> \<turnstile>
      ?Ax2 : Prop"
    using typed_caie_wname_dsim_surrogacy_principle
    by (intro weakening_front)
  have Q_type: "caie_classifier_ty # caie_classifier_ty # \<Gamma> \<turnstile>
      Var 1 : caie_classifier_ty"
    by simp
  have Z_type: "caie_classifier_ty # caie_classifier_ty # \<Gamma> \<turnstile>
      Var 0 : caie_classifier_ty"
    by simp
  have Ante_type: "caie_classifier_ty # caie_classifier_ty # \<Gamma> \<turnstile>
      ?Ante : Prop"
    by (rule infer_type_sound)
      (simp add: caie_term_defs caie_type_defs lookup_def eval_nat_numeral)
  have Dsim_type: "caie_classifier_ty # caie_classifier_ty # \<Gamma> \<turnstile>
      ?Dsim : Prop"
    using Q_type Z_type by (rule typed_caie_dsim)
  have DownEq_type: "caie_classifier_ty # caie_classifier_ty # \<Gamma> \<turnstile>
      ?DownEq : Prop"
    by (rule infer_type_sound)
      (simp add: caie_term_defs caie_type_defs lookup_def eval_nat_numeral)
  have BoxCond_type: "caie_classifier_ty # caie_classifier_ty # \<Gamma> \<turnstile>
      ?BoxCond : Prop"
    by (rule infer_type_sound)
      (simp add: caie_term_defs caie_type_defs lookup_def eval_nat_numeral)
  have DownBic_type: "caie_classifier_ty # caie_classifier_ty # \<Gamma> \<turnstile>
      ?DownBic : Prop"
    using DownEq_type BoxCond_type by auto
  have OfficialBic_type: "caie_classifier_ty # caie_classifier_ty # \<Gamma> \<turnstile>
      ?OfficialBic : Prop"
    using Dsim_type BoxCond_type by auto
  have inst_deriv: "caie_classifier_ty # caie_classifier_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp ?Ax2 (Imp ?Ante ?DownBic)"
    by (rule CEV_caie_wname_dsim_surrogacy_instance)
  have dsim_bridge: "caie_classifier_ty # caie_classifier_ty # \<Gamma> \<turnstile>\<^sub>CEV
      (?Dsim \<longleftrightarrow>\<^sub>o ?DownEq)"
    using Q_type Z_type by (rule CEV_caie_dsim)
  have down_to_official: "caie_classifier_ty # caie_classifier_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp ?DownBic ?OfficialBic"
    using Dsim_type DownEq_type BoxCond_type dsim_bridge
    by (rule CEV_bicond_replace_left)
  have lift_under_ante: "caie_classifier_ty # caie_classifier_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp (Imp ?Ante ?DownBic) (Imp ?Ante ?OfficialBic)"
    using Ante_type DownBic_type OfficialBic_type down_to_official
    by (rule CEV_imp_lift_right)
  have AnteDown_type: "caie_classifier_ty # caie_classifier_ty # \<Gamma> \<turnstile>
      Imp ?Ante ?DownBic : Prop"
    using Ante_type DownBic_type by auto
  have InnerBody_type0: "caie_classifier_ty # caie_classifier_ty # \<Gamma> \<turnstile>
      ?InnerBody : Prop"
    using Ante_type OfficialBic_type by auto
  have ax2_to_official: "caie_classifier_ty # caie_classifier_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp ?Ax2 ?InnerBody"
    using Ax2_type AnteDown_type InnerBody_type0 inst_deriv lift_under_ante
    by (rule CEV_imp_trans)
  have ax2_to_official_shifted:
      "caie_classifier_ty # caie_classifier_ty # \<Gamma> \<turnstile>\<^sub>CEV
        Imp (shift ?Ax1) ?InnerBody"
    using ax2_to_official by (simp add: shift_def)
  have Ax1_type: "caie_classifier_ty # \<Gamma> \<turnstile> ?Ax1 : Prop"
    using typed_caie_wname_dsim_surrogacy_principle
    by (rule weakening_front)
  have InnerBody_type: "caie_classifier_ty # caie_classifier_ty # \<Gamma> \<turnstile>
      ?InnerBody : Prop"
    using Ante_type OfficialBic_type by auto
  have inner_gen: "caie_classifier_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp ?Ax1 (Forall caie_classifier_ty ?InnerBody)"
    using Ax1_type InnerBody_type ax2_to_official_shifted
    by (rule CEV_proves.Gen)
  have Ax_type: "\<Gamma> \<turnstile> ?Ax : Prop"
    by (rule typed_caie_wname_dsim_surrogacy_principle)
  have ForallInner_type: "caie_classifier_ty # \<Gamma> \<turnstile>
      Forall caie_classifier_ty ?InnerBody : Prop"
    using InnerBody_type by auto
  have outer_gen: "\<Gamma> \<turnstile>\<^sub>CEV
      Imp ?Ax (Forall caie_classifier_ty (Forall caie_classifier_ty ?InnerBody))"
    using Ax_type ForallInner_type inner_gen by (rule CEV_proves.Gen)
  then show ?thesis
    by (simp add: caie_Thm38_def)
qed

lemma beta_eta_caie_Thm38_wname_dsim_surrogacy:
  "beta_eta_equiv \<Gamma> Prop caie_Thm38 caie_wname_dsim_surrogacy_principle"
proof -
  let ?Ante = "Conj (caie_WName (Var 1)) (caie_WName (Var 0))"
  let ?Dsim = "Var 1 \<sim>\<^sub>\<down>c Var 0"
  let ?DownEq =
    "Eq caie_prop_ty ((Var 1)\<^sup>\<down>\<^sub>c) ((Var 0)\<^sup>\<down>\<^sub>c)"
  let ?BoxCond =
    "\<box>\<^sub>o
      (Imp
        (Exists Ind
          (Disj
            (Eq caie_classifier_ty (Var 2)
              (Lam caie_prop_ty (App (Var 0) (Var 1))))
            (Eq caie_classifier_ty (Var 1)
              (Lam caie_prop_ty (App (Var 0) (Var 1))))))
        (Eq caie_classifier_ty (Var 1) (Var 0)))"
  let ?OfficialBic = "?Dsim \<longleftrightarrow>\<^sub>o ?BoxCond"
  let ?ExpandedBic = "?DownEq \<longleftrightarrow>\<^sub>o ?BoxCond"
  let ?OfficialBody = "Imp ?Ante ?OfficialBic"
  let ?ExpandedBody = "Imp ?Ante ?ExpandedBic"
  have Q_type: "caie_classifier_ty # caie_classifier_ty # \<Gamma> \<turnstile>
      Var 1 : caie_classifier_ty"
    by simp
  have Z_type: "caie_classifier_ty # caie_classifier_ty # \<Gamma> \<turnstile>
      Var 0 : caie_classifier_ty"
    by simp
  have Ante_type: "caie_classifier_ty # caie_classifier_ty # \<Gamma> \<turnstile>
      ?Ante : Prop"
    by (rule infer_type_sound)
      (simp add: caie_term_defs caie_type_defs lookup_def eval_nat_numeral)
  have BoxCond_type: "caie_classifier_ty # caie_classifier_ty # \<Gamma> \<turnstile>
      ?BoxCond : Prop"
    by (rule infer_type_sound)
      (simp add: caie_term_defs caie_type_defs lookup_def eval_nat_numeral)
  have dsim_eqv: "beta_eta_equiv
      (caie_classifier_ty # caie_classifier_ty # \<Gamma>) Prop ?Dsim ?DownEq"
    using Q_type Z_type by (rule beta_eta_caie_dsim)
  have bicond_eqv: "beta_eta_equiv
      (caie_classifier_ty # caie_classifier_ty # \<Gamma>) Prop
        ?OfficialBic ?ExpandedBic"
    using dsim_eqv BoxCond_type by (rule beta_eta_equiv_Bicond_left)
  have body_eqv: "beta_eta_equiv
      (caie_classifier_ty # caie_classifier_ty # \<Gamma>) Prop
        ?OfficialBody ?ExpandedBody"
    using Ante_type bicond_eqv by (rule beta_eta_equiv_Imp_right)
  have inner_forall_eqv: "beta_eta_equiv (caie_classifier_ty # \<Gamma>) Prop
      (Forall caie_classifier_ty ?OfficialBody)
      (Forall caie_classifier_ty ?ExpandedBody)"
    using body_eqv by (rule beta_eta_equiv_Forall_body)
  have outer_forall_eqv: "beta_eta_equiv \<Gamma> Prop
      (Forall caie_classifier_ty (Forall caie_classifier_ty ?OfficialBody))
      (Forall caie_classifier_ty (Forall caie_classifier_ty ?ExpandedBody))"
    using inner_forall_eqv by (rule beta_eta_equiv_Forall_body)
  then show ?thesis
    by (simp add: caie_Thm38_def caie_wname_dsim_surrogacy_principle_def)
qed

lemma CEV_caie_Thm38_wname_dsim_surrogacy:
  "\<Gamma> \<turnstile>\<^sub>CEV
    (caie_Thm38 \<longleftrightarrow>\<^sub>o caie_wname_dsim_surrogacy_principle)"
  using beta_eta_caie_Thm38_wname_dsim_surrogacy
  by (rule CEV_beta_eta_equiv)

lemma caie_CEV_derivable_Thm38_wname_dsim_surrogacy_bridge:
  "caie_CEV_derivable \<Gamma> \<Delta>
    (caie_Thm38 \<longleftrightarrow>\<^sub>o caie_wname_dsim_surrogacy_principle)"
  using CEV_caie_Thm38_wname_dsim_surrogacy
  by (rule caie_CEV_derivable_of_theorem)

lemma caie_CEV_derivable_Thm38_from_axiom_package:
  "caie_CEV_derivable \<Gamma> caie_appendix_C_axiom_package caie_Thm38"
proof -
  have member:
      "caie_wname_dsim_surrogacy_principle \<in>
        set caie_appendix_C_axiom_package"
    by (simp add: caie_appendix_C_axiom_package_def
        caie_name_haecceity_principles_def)
  have d_ax: "caie_CEV_derivable \<Gamma> caie_appendix_C_axiom_package
      caie_wname_dsim_surrogacy_principle"
    using member by (rule caie_CEV_derivable_appendix_C_axiom)
  have thm38_type: "\<Gamma> \<turnstile> caie_Thm38 : Prop"
    by (rule typed_caie_Thm38)
  have surrogate_type:
      "\<Gamma> \<turnstile> caie_wname_dsim_surrogacy_principle : Prop"
    by (rule typed_caie_wname_dsim_surrogacy_principle)
  have d_bridge: "caie_CEV_derivable \<Gamma> caie_appendix_C_axiom_package
      (caie_Thm38 \<longleftrightarrow>\<^sub>o caie_wname_dsim_surrogacy_principle)"
    by (rule caie_CEV_derivable_Thm38_wname_dsim_surrogacy_bridge)
  show ?thesis
    using thm38_type surrogate_type d_bridge d_ax
    by (rule caie_CEV_derivable_bicond_right)
qed

lemma caie_appendix_C_seventh_residual_target_from_axiom_package:
  "caie_CEV_derivable \<Gamma> caie_appendix_C_axiom_package caie_Thm38"
  by (rule caie_CEV_derivable_Thm38_from_axiom_package)


subsection \<open>Appendix C Theorem 39 from the axiom package\<close>

lemma CEV_caie_hae_wname_dsim_identity_surrogacy_instance:
  "caie_classifier_ty # caie_classifier_ty # \<Gamma> \<turnstile>\<^sub>CEV
    Imp (shift (shift caie_hae_wname_dsim_identity_surrogacy_principle))
      (Imp (Conj (caie_Hae (Var 1)) (caie_WName (Var 0)))
        (Eq caie_prop_ty ((Var 1)\<^sup>\<down>\<^sub>c) ((Var 0)\<^sup>\<down>\<^sub>c)
          \<longleftrightarrow>\<^sub>o Eq caie_classifier_ty (Var 1) (Var 0)))"
proof -
  let ?OuterBody =
    "Forall caie_classifier_ty
      (Imp (Conj (caie_Hae (Var 1)) (caie_WName (Var 0)))
        (Eq caie_prop_ty ((Var 1)\<^sup>\<down>\<^sub>c) ((Var 0)\<^sup>\<down>\<^sub>c)
          \<longleftrightarrow>\<^sub>o Eq caie_classifier_ty (Var 1) (Var 0)))"
  let ?LiftedOuterBody =
    "rename (lift_ren Suc) (rename (lift_ren Suc) ?OuterBody)"
  let ?ForallZ =
    "Forall caie_classifier_ty
      (Imp (Conj (caie_Hae (Var 2)) (caie_WName (Var 0)))
        (Eq caie_prop_ty ((Var 2)\<^sup>\<down>\<^sub>c) ((Var 0)\<^sup>\<down>\<^sub>c)
          \<longleftrightarrow>\<^sub>o Eq caie_classifier_ty (Var 2) (Var 0)))"
  let ?Inst =
    "Imp (Conj (caie_Hae (Var 1)) (caie_WName (Var 0)))
      (Eq caie_prop_ty ((Var 1)\<^sup>\<down>\<^sub>c) ((Var 0)\<^sup>\<down>\<^sub>c)
        \<longleftrightarrow>\<^sub>o Eq caie_classifier_ty (Var 1) (Var 0))"
  have outer_body_type: "caie_classifier_ty # \<Gamma> \<turnstile> ?OuterBody : Prop"
    by (rule infer_type_sound)
      (simp add: caie_term_defs caie_type_defs lookup_def)
  have lifted_outer_body_once_type:
      "caie_classifier_ty # caie_classifier_ty # \<Gamma> \<turnstile>
        rename (lift_ren Suc) ?OuterBody : Prop"
    using outer_body_type by (rule weakening_after_front)
  have lifted_outer_body_type:
      "caie_classifier_ty # caie_classifier_ty # caie_classifier_ty # \<Gamma> \<turnstile>
        ?LiftedOuterBody : Prop"
    using lifted_outer_body_once_type by (rule weakening_after_front)
  have var1_type:
      "caie_classifier_ty # caie_classifier_ty # \<Gamma> \<turnstile>
        Var 1 : caie_classifier_ty"
    by simp
  have outer_raw: "caie_classifier_ty # caie_classifier_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp (Forall caie_classifier_ty ?LiftedOuterBody)
        (subst0 (Var 1) ?LiftedOuterBody)"
    using lifted_outer_body_type var1_type by (rule CEV_forall_inst)
  have outer_ui: "caie_classifier_ty # caie_classifier_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp (shift (shift caie_hae_wname_dsim_identity_surrogacy_principle))
        ?ForallZ"
    using outer_raw
    by (simp add: caie_hae_wname_dsim_identity_surrogacy_principle_def
      caie_term_defs caie_type_defs shift_def subst0_def eval_nat_numeral)
  have inner_body_type:
      "caie_classifier_ty # caie_classifier_ty # caie_classifier_ty # \<Gamma> \<turnstile>
        (Imp (Conj (caie_Hae (Var 2)) (caie_WName (Var 0)))
          (Eq caie_prop_ty ((Var 2)\<^sup>\<down>\<^sub>c) ((Var 0)\<^sup>\<down>\<^sub>c)
            \<longleftrightarrow>\<^sub>o Eq caie_classifier_ty (Var 2) (Var 0))) : Prop"
    by (rule infer_type_sound)
      (simp add: caie_term_defs caie_type_defs lookup_def)
  have var0_type:
      "caie_classifier_ty # caie_classifier_ty # \<Gamma> \<turnstile>
        Var 0 : caie_classifier_ty"
    by simp
  have inner_raw: "caie_classifier_ty # caie_classifier_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp ?ForallZ
        (subst0 (Var 0)
          (Imp (Conj (caie_Hae (Var 2)) (caie_WName (Var 0)))
            (Eq caie_prop_ty ((Var 2)\<^sup>\<down>\<^sub>c) ((Var 0)\<^sup>\<down>\<^sub>c)
              \<longleftrightarrow>\<^sub>o Eq caie_classifier_ty (Var 2) (Var 0))))"
    using inner_body_type var0_type by (rule CEV_forall_inst)
  have inner_ui: "caie_classifier_ty # caie_classifier_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp ?ForallZ ?Inst"
    using inner_raw
    by (simp add: caie_term_defs caie_type_defs subst0_def eval_nat_numeral)
  have shifted_principle_type:
      "caie_classifier_ty # caie_classifier_ty # \<Gamma> \<turnstile>
        shift (shift caie_hae_wname_dsim_identity_surrogacy_principle) : Prop"
    using typed_caie_hae_wname_dsim_identity_surrogacy_principle
    by (intro weakening_front)
  have forallZ_type:
      "caie_classifier_ty # caie_classifier_ty # \<Gamma> \<turnstile> ?ForallZ : Prop"
    by (rule infer_type_sound)
      (simp add: caie_term_defs caie_type_defs lookup_def)
  have inst_type:
      "caie_classifier_ty # caie_classifier_ty # \<Gamma> \<turnstile> ?Inst : Prop"
    by (rule infer_type_sound)
      (simp add: caie_term_defs caie_type_defs lookup_def)
  show ?thesis
    using shifted_principle_type forallZ_type inst_type outer_ui inner_ui
    by (rule CEV_imp_trans)
qed

lemma CEV_caie_Thm39_from_hae_wname_dsim_identity_surrogacy:
  "\<Gamma> \<turnstile>\<^sub>CEV
    Imp caie_hae_wname_dsim_identity_surrogacy_principle caie_Thm39"
proof -
  let ?Ax = "caie_hae_wname_dsim_identity_surrogacy_principle"
  let ?Ax1 = "shift ?Ax"
  let ?Ax2 = "shift (shift ?Ax)"
  let ?Ante = "Conj (caie_Hae (Var 1)) (caie_WName (Var 0))"
  let ?Dsim = "Var 1 \<sim>\<^sub>\<down>c Var 0"
  let ?DownEq =
    "Eq caie_prop_ty ((Var 1)\<^sup>\<down>\<^sub>c) ((Var 0)\<^sup>\<down>\<^sub>c)"
  let ?IdEq = "Eq caie_classifier_ty (Var 1) (Var 0)"
  let ?DownBic = "?DownEq \<longleftrightarrow>\<^sub>o ?IdEq"
  let ?OfficialBic = "?Dsim \<longleftrightarrow>\<^sub>o ?IdEq"
  let ?InnerBody = "Imp ?Ante ?OfficialBic"
  have Ax2_type: "caie_classifier_ty # caie_classifier_ty # \<Gamma> \<turnstile>
      ?Ax2 : Prop"
    using typed_caie_hae_wname_dsim_identity_surrogacy_principle
    by (intro weakening_front)
  have Q_type: "caie_classifier_ty # caie_classifier_ty # \<Gamma> \<turnstile>
      Var 1 : caie_classifier_ty"
    by simp
  have Z_type: "caie_classifier_ty # caie_classifier_ty # \<Gamma> \<turnstile>
      Var 0 : caie_classifier_ty"
    by simp
  have Ante_type: "caie_classifier_ty # caie_classifier_ty # \<Gamma> \<turnstile>
      ?Ante : Prop"
    by (rule infer_type_sound)
      (simp add: caie_term_defs caie_type_defs lookup_def eval_nat_numeral)
  have Dsim_type: "caie_classifier_ty # caie_classifier_ty # \<Gamma> \<turnstile>
      ?Dsim : Prop"
    using Q_type Z_type by (rule typed_caie_dsim)
  have DownEq_type: "caie_classifier_ty # caie_classifier_ty # \<Gamma> \<turnstile>
      ?DownEq : Prop"
    by (rule infer_type_sound)
      (simp add: caie_term_defs caie_type_defs lookup_def eval_nat_numeral)
  have IdEq_type: "caie_classifier_ty # caie_classifier_ty # \<Gamma> \<turnstile>
      ?IdEq : Prop"
    using Q_type Z_type by auto
  have DownBic_type: "caie_classifier_ty # caie_classifier_ty # \<Gamma> \<turnstile>
      ?DownBic : Prop"
    using DownEq_type IdEq_type by auto
  have OfficialBic_type: "caie_classifier_ty # caie_classifier_ty # \<Gamma> \<turnstile>
      ?OfficialBic : Prop"
    using Dsim_type IdEq_type by auto
  have inst_deriv: "caie_classifier_ty # caie_classifier_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp ?Ax2 (Imp ?Ante ?DownBic)"
    by (rule CEV_caie_hae_wname_dsim_identity_surrogacy_instance)
  have dsim_bridge: "caie_classifier_ty # caie_classifier_ty # \<Gamma> \<turnstile>\<^sub>CEV
      (?Dsim \<longleftrightarrow>\<^sub>o ?DownEq)"
    using Q_type Z_type by (rule CEV_caie_dsim)
  have down_to_official: "caie_classifier_ty # caie_classifier_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp ?DownBic ?OfficialBic"
    using Dsim_type DownEq_type IdEq_type dsim_bridge
    by (rule CEV_bicond_replace_left)
  have lift_under_ante: "caie_classifier_ty # caie_classifier_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp (Imp ?Ante ?DownBic) (Imp ?Ante ?OfficialBic)"
    using Ante_type DownBic_type OfficialBic_type down_to_official
    by (rule CEV_imp_lift_right)
  have AnteDown_type: "caie_classifier_ty # caie_classifier_ty # \<Gamma> \<turnstile>
      Imp ?Ante ?DownBic : Prop"
    using Ante_type DownBic_type by auto
  have InnerBody_type0: "caie_classifier_ty # caie_classifier_ty # \<Gamma> \<turnstile>
      ?InnerBody : Prop"
    using Ante_type OfficialBic_type by auto
  have ax2_to_official: "caie_classifier_ty # caie_classifier_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp ?Ax2 ?InnerBody"
    using Ax2_type AnteDown_type InnerBody_type0 inst_deriv lift_under_ante
    by (rule CEV_imp_trans)
  have ax2_to_official_shifted:
      "caie_classifier_ty # caie_classifier_ty # \<Gamma> \<turnstile>\<^sub>CEV
        Imp (shift ?Ax1) ?InnerBody"
    using ax2_to_official by (simp add: shift_def)
  have Ax1_type: "caie_classifier_ty # \<Gamma> \<turnstile> ?Ax1 : Prop"
    using typed_caie_hae_wname_dsim_identity_surrogacy_principle
    by (rule weakening_front)
  have InnerBody_type: "caie_classifier_ty # caie_classifier_ty # \<Gamma> \<turnstile>
      ?InnerBody : Prop"
    using Ante_type OfficialBic_type by auto
  have inner_gen: "caie_classifier_ty # \<Gamma> \<turnstile>\<^sub>CEV
      Imp ?Ax1 (Forall caie_classifier_ty ?InnerBody)"
    using Ax1_type InnerBody_type ax2_to_official_shifted
    by (rule CEV_proves.Gen)
  have Ax_type: "\<Gamma> \<turnstile> ?Ax : Prop"
    by (rule typed_caie_hae_wname_dsim_identity_surrogacy_principle)
  have ForallInner_type: "caie_classifier_ty # \<Gamma> \<turnstile>
      Forall caie_classifier_ty ?InnerBody : Prop"
    using InnerBody_type by auto
  have outer_gen: "\<Gamma> \<turnstile>\<^sub>CEV
      Imp ?Ax (Forall caie_classifier_ty (Forall caie_classifier_ty ?InnerBody))"
    using Ax_type ForallInner_type inner_gen by (rule CEV_proves.Gen)
  then show ?thesis
    by (simp add: caie_Thm39_def)
qed

lemma beta_eta_caie_Thm39_hae_wname_dsim_identity_surrogacy:
  "beta_eta_equiv \<Gamma> Prop caie_Thm39
    caie_hae_wname_dsim_identity_surrogacy_principle"
proof -
  let ?Ante = "Conj (caie_Hae (Var 1)) (caie_WName (Var 0))"
  let ?Dsim = "Var 1 \<sim>\<^sub>\<down>c Var 0"
  let ?DownEq =
    "Eq caie_prop_ty ((Var 1)\<^sup>\<down>\<^sub>c) ((Var 0)\<^sup>\<down>\<^sub>c)"
  let ?IdEq = "Eq caie_classifier_ty (Var 1) (Var 0)"
  let ?OfficialBic = "?Dsim \<longleftrightarrow>\<^sub>o ?IdEq"
  let ?ExpandedBic = "?DownEq \<longleftrightarrow>\<^sub>o ?IdEq"
  let ?OfficialBody = "Imp ?Ante ?OfficialBic"
  let ?ExpandedBody = "Imp ?Ante ?ExpandedBic"
  have Q_type: "caie_classifier_ty # caie_classifier_ty # \<Gamma> \<turnstile>
      Var 1 : caie_classifier_ty"
    by simp
  have Z_type: "caie_classifier_ty # caie_classifier_ty # \<Gamma> \<turnstile>
      Var 0 : caie_classifier_ty"
    by simp
  have Ante_type: "caie_classifier_ty # caie_classifier_ty # \<Gamma> \<turnstile>
      ?Ante : Prop"
    by (rule infer_type_sound)
      (simp add: caie_term_defs caie_type_defs lookup_def eval_nat_numeral)
  have IdEq_type: "caie_classifier_ty # caie_classifier_ty # \<Gamma> \<turnstile>
      ?IdEq : Prop"
    using Q_type Z_type by auto
  have dsim_eqv: "beta_eta_equiv
      (caie_classifier_ty # caie_classifier_ty # \<Gamma>) Prop ?Dsim ?DownEq"
    using Q_type Z_type by (rule beta_eta_caie_dsim)
  have bicond_eqv: "beta_eta_equiv
      (caie_classifier_ty # caie_classifier_ty # \<Gamma>) Prop
        ?OfficialBic ?ExpandedBic"
    using dsim_eqv IdEq_type by (rule beta_eta_equiv_Bicond_left)
  have body_eqv: "beta_eta_equiv
      (caie_classifier_ty # caie_classifier_ty # \<Gamma>) Prop
        ?OfficialBody ?ExpandedBody"
    using Ante_type bicond_eqv by (rule beta_eta_equiv_Imp_right)
  have inner_forall_eqv: "beta_eta_equiv (caie_classifier_ty # \<Gamma>) Prop
      (Forall caie_classifier_ty ?OfficialBody)
      (Forall caie_classifier_ty ?ExpandedBody)"
    using body_eqv by (rule beta_eta_equiv_Forall_body)
  have outer_forall_eqv: "beta_eta_equiv \<Gamma> Prop
      (Forall caie_classifier_ty (Forall caie_classifier_ty ?OfficialBody))
      (Forall caie_classifier_ty (Forall caie_classifier_ty ?ExpandedBody))"
    using inner_forall_eqv by (rule beta_eta_equiv_Forall_body)
  then show ?thesis
    by (simp add: caie_Thm39_def
      caie_hae_wname_dsim_identity_surrogacy_principle_def)
qed

lemma CEV_caie_Thm39_hae_wname_dsim_identity_surrogacy:
  "\<Gamma> \<turnstile>\<^sub>CEV
    (caie_Thm39 \<longleftrightarrow>\<^sub>o
      caie_hae_wname_dsim_identity_surrogacy_principle)"
  using beta_eta_caie_Thm39_hae_wname_dsim_identity_surrogacy
  by (rule CEV_beta_eta_equiv)

lemma caie_CEV_derivable_Thm39_hae_wname_dsim_identity_surrogacy_bridge:
  "caie_CEV_derivable \<Gamma> \<Delta>
    (caie_Thm39 \<longleftrightarrow>\<^sub>o
      caie_hae_wname_dsim_identity_surrogacy_principle)"
  using CEV_caie_Thm39_hae_wname_dsim_identity_surrogacy
  by (rule caie_CEV_derivable_of_theorem)

lemma caie_CEV_derivable_Thm39_from_axiom_package:
  "caie_CEV_derivable \<Gamma> caie_appendix_C_axiom_package caie_Thm39"
proof -
  have member:
      "caie_hae_wname_dsim_identity_surrogacy_principle \<in>
        set caie_appendix_C_axiom_package"
    by (simp add: caie_appendix_C_axiom_package_def
        caie_name_haecceity_principles_def)
  have d_ax: "caie_CEV_derivable \<Gamma> caie_appendix_C_axiom_package
      caie_hae_wname_dsim_identity_surrogacy_principle"
    using member by (rule caie_CEV_derivable_appendix_C_axiom)
  have thm39_type: "\<Gamma> \<turnstile> caie_Thm39 : Prop"
    by (rule typed_caie_Thm39)
  have surrogate_type:
      "\<Gamma> \<turnstile> caie_hae_wname_dsim_identity_surrogacy_principle : Prop"
    by (rule typed_caie_hae_wname_dsim_identity_surrogacy_principle)
  have d_bridge: "caie_CEV_derivable \<Gamma> caie_appendix_C_axiom_package
      (caie_Thm39 \<longleftrightarrow>\<^sub>o
        caie_hae_wname_dsim_identity_surrogacy_principle)"
    by (rule caie_CEV_derivable_Thm39_hae_wname_dsim_identity_surrogacy_bridge)
  show ?thesis
    using thm39_type surrogate_type d_bridge d_ax
    by (rule caie_CEV_derivable_bicond_right)
qed

lemma caie_appendix_C_eighth_residual_target_from_axiom_package:
  "caie_CEV_derivable \<Gamma> caie_appendix_C_axiom_package caie_Thm39"
  by (rule caie_CEV_derivable_Thm39_from_axiom_package)


subsection \<open>Appendix C Theorem 40 from the axiom package\<close>

lemma beta_eta_caie_Thm40_down_eq_surrogacy:
  "beta_eta_equiv \<Gamma> Prop caie_Thm40
    caie_wname_unique_name_down_eq_surrogacy_principle"
proof -
  let ?InnerOfficial =
    "Imp
      (Conj (caie_Name (Var 0)) (Var 2 \<sim>\<^sub>\<down>c Var 0))
      (Eq caie_classifier_ty (Var 0) (Var 1))"
  let ?InnerExpanded =
    "Imp
      (Conj (caie_Name (Var 0))
        (Eq caie_prop_ty ((Var 2)\<^sup>\<down>\<^sub>c) ((Var 0)\<^sup>\<down>\<^sub>c)))
      (Eq caie_classifier_ty (Var 0) (Var 1))"
  let ?ForallOfficial = "Forall caie_classifier_ty ?InnerOfficial"
  let ?ForallExpanded = "Forall caie_classifier_ty ?InnerExpanded"
  let ?ExistsBodyOfficial =
    "Conj (caie_Name (Var 0))
      (Conj (Var 1 \<sim>\<^sub>\<down>c Var 0) ?ForallOfficial)"
  let ?ExistsBodyExpanded =
    "Conj (caie_Name (Var 0))
      (Conj
        (Eq caie_prop_ty ((Var 1)\<^sup>\<down>\<^sub>c) ((Var 0)\<^sup>\<down>\<^sub>c))
        ?ForallExpanded)"
  let ?OuterBodyOfficial =
    "Imp (caie_WName (Var 0)) (Exists caie_classifier_ty ?ExistsBodyOfficial)"
  let ?OuterBodyExpanded =
    "Imp (caie_WName (Var 0)) (Exists caie_classifier_ty ?ExistsBodyExpanded)"

  have R_type: "caie_classifier_ty # caie_classifier_ty # caie_classifier_ty # \<Gamma>
      \<turnstile> Var 0 : caie_classifier_ty"
    by (simp add: lookup_def)
  have Q_type_inner:
      "caie_classifier_ty # caie_classifier_ty # caie_classifier_ty # \<Gamma>
        \<turnstile> Var 1 : caie_classifier_ty"
    by (simp add: lookup_def)
  have Z_type_inner:
      "caie_classifier_ty # caie_classifier_ty # caie_classifier_ty # \<Gamma>
        \<turnstile> Var 2 : caie_classifier_ty"
    by (simp add: lookup_def)
  have InnerName_type:
      "caie_classifier_ty # caie_classifier_ty # caie_classifier_ty # \<Gamma>
        \<turnstile> caie_Name (Var 0) : Prop"
    using R_type by (rule typed_caie_Name)
  have InnerDsim_type:
      "caie_classifier_ty # caie_classifier_ty # caie_classifier_ty # \<Gamma>
        \<turnstile> Var 2 \<sim>\<^sub>\<down>c Var 0 : Prop"
    using Z_type_inner R_type by (rule typed_caie_dsim)
  have InnerDownEq_type:
      "caie_classifier_ty # caie_classifier_ty # caie_classifier_ty # \<Gamma>
        \<turnstile> Eq caie_prop_ty ((Var 2)\<^sup>\<down>\<^sub>c) ((Var 0)\<^sup>\<down>\<^sub>c) : Prop"
    by (rule infer_type_sound)
      (simp add: caie_term_defs caie_type_defs lookup_def)
  have InnerEq_type:
      "caie_classifier_ty # caie_classifier_ty # caie_classifier_ty # \<Gamma>
        \<turnstile> Eq caie_classifier_ty (Var 0) (Var 1) : Prop"
    using R_type Q_type_inner by auto
  have InnerAnteOfficial_type:
      "caie_classifier_ty # caie_classifier_ty # caie_classifier_ty # \<Gamma>
        \<turnstile> Conj (caie_Name (Var 0)) (Var 2 \<sim>\<^sub>\<down>c Var 0) : Prop"
    using InnerName_type InnerDsim_type by auto
  have InnerAnteExpanded_type:
      "caie_classifier_ty # caie_classifier_ty # caie_classifier_ty # \<Gamma>
        \<turnstile> Conj (caie_Name (Var 0))
          (Eq caie_prop_ty ((Var 2)\<^sup>\<down>\<^sub>c) ((Var 0)\<^sup>\<down>\<^sub>c)) : Prop"
    using InnerName_type InnerDownEq_type by auto
  have InnerOfficial_type:
      "caie_classifier_ty # caie_classifier_ty # caie_classifier_ty # \<Gamma>
        \<turnstile> ?InnerOfficial : Prop"
    using InnerAnteOfficial_type InnerEq_type by auto
  have InnerExpanded_type:
      "caie_classifier_ty # caie_classifier_ty # caie_classifier_ty # \<Gamma>
        \<turnstile> ?InnerExpanded : Prop"
    using InnerAnteExpanded_type InnerEq_type by auto
  have inner_dsim_eqv:
      "beta_eta_equiv
        (caie_classifier_ty # caie_classifier_ty # caie_classifier_ty # \<Gamma>)
        Prop (Var 2 \<sim>\<^sub>\<down>c Var 0)
          (Eq caie_prop_ty ((Var 2)\<^sup>\<down>\<^sub>c) ((Var 0)\<^sup>\<down>\<^sub>c))"
    using Z_type_inner R_type by (rule beta_eta_caie_dsim)
  have inner_ante_eqv:
      "beta_eta_equiv
        (caie_classifier_ty # caie_classifier_ty # caie_classifier_ty # \<Gamma>)
        Prop
          (Conj (caie_Name (Var 0)) (Var 2 \<sim>\<^sub>\<down>c Var 0))
          (Conj (caie_Name (Var 0))
            (Eq caie_prop_ty ((Var 2)\<^sup>\<down>\<^sub>c) ((Var 0)\<^sup>\<down>\<^sub>c)))"
    using InnerName_type inner_dsim_eqv by (rule beta_eta_equiv_Conj_right)
  have inner_body_eqv:
      "beta_eta_equiv
        (caie_classifier_ty # caie_classifier_ty # caie_classifier_ty # \<Gamma>)
        Prop ?InnerOfficial ?InnerExpanded"
    using inner_ante_eqv InnerEq_type by (rule beta_eta_equiv_Imp_left)
  have forall_eqv:
      "beta_eta_equiv (caie_classifier_ty # caie_classifier_ty # \<Gamma>)
        Prop ?ForallOfficial ?ForallExpanded"
    using inner_body_eqv by (rule beta_eta_equiv_Forall_body)

  have Q_type:
      "caie_classifier_ty # caie_classifier_ty # \<Gamma> \<turnstile>
        Var 0 : caie_classifier_ty"
    by (simp add: lookup_def)
  have Z_type:
      "caie_classifier_ty # caie_classifier_ty # \<Gamma> \<turnstile>
        Var 1 : caie_classifier_ty"
    by (simp add: lookup_def)
  have NameQ_type:
      "caie_classifier_ty # caie_classifier_ty # \<Gamma> \<turnstile>
        caie_Name (Var 0) : Prop"
    using Q_type by (rule typed_caie_Name)
  have OuterDsim_type:
      "caie_classifier_ty # caie_classifier_ty # \<Gamma> \<turnstile>
        Var 1 \<sim>\<^sub>\<down>c Var 0 : Prop"
    using Z_type Q_type by (rule typed_caie_dsim)
  have OuterDownEq_type:
      "caie_classifier_ty # caie_classifier_ty # \<Gamma> \<turnstile>
        Eq caie_prop_ty ((Var 1)\<^sup>\<down>\<^sub>c) ((Var 0)\<^sup>\<down>\<^sub>c) : Prop"
    by (rule infer_type_sound)
      (simp add: caie_term_defs caie_type_defs lookup_def)
  have ForallOfficial_type:
      "caie_classifier_ty # caie_classifier_ty # \<Gamma> \<turnstile>
        ?ForallOfficial : Prop"
    using InnerOfficial_type by auto
  have ForallExpanded_type:
      "caie_classifier_ty # caie_classifier_ty # \<Gamma> \<turnstile>
        ?ForallExpanded : Prop"
    using InnerExpanded_type by auto
  have outer_dsim_eqv:
      "beta_eta_equiv (caie_classifier_ty # caie_classifier_ty # \<Gamma>)
        Prop (Var 1 \<sim>\<^sub>\<down>c Var 0)
          (Eq caie_prop_ty ((Var 1)\<^sup>\<down>\<^sub>c) ((Var 0)\<^sup>\<down>\<^sub>c))"
    using Z_type Q_type by (rule beta_eta_caie_dsim)
  have tail_left_eqv:
      "beta_eta_equiv (caie_classifier_ty # caie_classifier_ty # \<Gamma>)
        Prop
          (Conj (Var 1 \<sim>\<^sub>\<down>c Var 0) ?ForallOfficial)
          (Conj
            (Eq caie_prop_ty ((Var 1)\<^sup>\<down>\<^sub>c) ((Var 0)\<^sup>\<down>\<^sub>c))
            ?ForallOfficial)"
    using outer_dsim_eqv ForallOfficial_type by (rule beta_eta_equiv_Conj_left)
  have tail_mid_type:
      "caie_classifier_ty # caie_classifier_ty # \<Gamma> \<turnstile>
        Conj
          (Eq caie_prop_ty ((Var 1)\<^sup>\<down>\<^sub>c) ((Var 0)\<^sup>\<down>\<^sub>c))
          ?ForallOfficial : Prop"
    using OuterDownEq_type ForallOfficial_type by auto
  have tail_right_eqv:
      "beta_eta_equiv (caie_classifier_ty # caie_classifier_ty # \<Gamma>)
        Prop
          (Conj
            (Eq caie_prop_ty ((Var 1)\<^sup>\<down>\<^sub>c) ((Var 0)\<^sup>\<down>\<^sub>c))
            ?ForallOfficial)
          (Conj
            (Eq caie_prop_ty ((Var 1)\<^sup>\<down>\<^sub>c) ((Var 0)\<^sup>\<down>\<^sub>c))
            ?ForallExpanded)"
    using OuterDownEq_type forall_eqv by (rule beta_eta_equiv_Conj_right)
  have tail_eqv:
      "beta_eta_equiv (caie_classifier_ty # caie_classifier_ty # \<Gamma>)
        Prop
          (Conj (Var 1 \<sim>\<^sub>\<down>c Var 0) ?ForallOfficial)
          (Conj
            (Eq caie_prop_ty ((Var 1)\<^sup>\<down>\<^sub>c) ((Var 0)\<^sup>\<down>\<^sub>c))
            ?ForallExpanded)"
    using tail_left_eqv tail_right_eqv by (rule beta_eta_equiv.Trans)
  have exists_body_eqv:
      "beta_eta_equiv (caie_classifier_ty # caie_classifier_ty # \<Gamma>)
        Prop ?ExistsBodyOfficial ?ExistsBodyExpanded"
    using NameQ_type tail_eqv by (rule beta_eta_equiv_Conj_right)
  have exists_eqv:
      "beta_eta_equiv (caie_classifier_ty # \<Gamma>) Prop
        (Exists caie_classifier_ty ?ExistsBodyOfficial)
        (Exists caie_classifier_ty ?ExistsBodyExpanded)"
    using exists_body_eqv by (rule beta_eta_equiv_Exists_body)

  have WName_type:
      "caie_classifier_ty # \<Gamma> \<turnstile> caie_WName (Var 0) : Prop"
    by (rule infer_type_sound)
      (simp add: caie_term_defs caie_type_defs lookup_def)
  have outer_body_eqv:
      "beta_eta_equiv (caie_classifier_ty # \<Gamma>) Prop
        ?OuterBodyOfficial ?OuterBodyExpanded"
    using WName_type exists_eqv by (rule beta_eta_equiv_Imp_right)
  have final_eqv:
      "beta_eta_equiv \<Gamma> Prop
        (Forall caie_classifier_ty ?OuterBodyOfficial)
        (Forall caie_classifier_ty ?OuterBodyExpanded)"
    using outer_body_eqv by (rule beta_eta_equiv_Forall_body)
  then show ?thesis
    by (simp add: caie_Thm40_def
      caie_wname_unique_name_down_eq_surrogacy_principle_def)
qed

lemma CEV_caie_Thm40_down_eq_surrogacy:
  "\<Gamma> \<turnstile>\<^sub>CEV
    (caie_Thm40 \<longleftrightarrow>\<^sub>o caie_wname_unique_name_down_eq_surrogacy_principle)"
  using beta_eta_caie_Thm40_down_eq_surrogacy
  by (rule CEV_beta_eta_equiv)

lemma caie_CEV_derivable_Thm40_down_eq_surrogacy_bridge:
  "caie_CEV_derivable \<Gamma> \<Delta>
    (caie_Thm40 \<longleftrightarrow>\<^sub>o caie_wname_unique_name_down_eq_surrogacy_principle)"
  using CEV_caie_Thm40_down_eq_surrogacy
  by (rule caie_CEV_derivable_of_theorem)

lemma CEV_caie_Thm40_of_down_eq_surrogacy:
  "\<Gamma> \<turnstile>\<^sub>CEV
    Imp caie_wname_unique_name_down_eq_surrogacy_principle caie_Thm40"
proof -
  have thm40_type: "\<Gamma> \<turnstile> caie_Thm40 : Prop"
    by (rule typed_caie_Thm40)
  have surrogate_type:
      "\<Gamma> \<turnstile> caie_wname_unique_name_down_eq_surrogacy_principle : Prop"
    by (rule typed_caie_wname_unique_name_down_eq_surrogacy_principle)
  have bicond: "\<Gamma> \<turnstile>\<^sub>CEV
      (caie_Thm40 \<longleftrightarrow>\<^sub>o
        caie_wname_unique_name_down_eq_surrogacy_principle)"
    by (rule CEV_caie_Thm40_down_eq_surrogacy)
  show ?thesis
    using thm40_type surrogate_type bicond by (rule CEV_beta_right_imp)
qed

lemma caie_CEV_derivable_Thm40_from_axiom_package:
  "caie_CEV_derivable \<Gamma> caie_appendix_C_axiom_package caie_Thm40"
proof -
  have member:
      "caie_wname_unique_name_down_eq_surrogacy_principle \<in>
        set caie_appendix_C_axiom_package"
    by (simp add: caie_appendix_C_axiom_package_def
        caie_name_haecceity_principles_def)
  have d_ax: "caie_CEV_derivable \<Gamma> caie_appendix_C_axiom_package
      caie_wname_unique_name_down_eq_surrogacy_principle"
    using member by (rule caie_CEV_derivable_appendix_C_axiom)
  have thm40_type: "\<Gamma> \<turnstile> caie_Thm40 : Prop"
    by (rule typed_caie_Thm40)
  have surrogate_type:
      "\<Gamma> \<turnstile> caie_wname_unique_name_down_eq_surrogacy_principle : Prop"
    by (rule typed_caie_wname_unique_name_down_eq_surrogacy_principle)
  have d_bridge: "caie_CEV_derivable \<Gamma> caie_appendix_C_axiom_package
      (caie_Thm40 \<longleftrightarrow>\<^sub>o
        caie_wname_unique_name_down_eq_surrogacy_principle)"
    by (rule caie_CEV_derivable_Thm40_down_eq_surrogacy_bridge)
  show ?thesis
    using thm40_type surrogate_type d_bridge d_ax
    by (rule caie_CEV_derivable_bicond_right)
qed

lemma caie_appendix_C_ninth_residual_target_from_axiom_package:
  "caie_CEV_derivable \<Gamma> caie_appendix_C_axiom_package caie_Thm40"
  by (rule caie_CEV_derivable_Thm40_from_axiom_package)

lemma caie_appendix_C_residual_target_from_axiom_package:
  assumes "A \<in> set caie_appendix_C_theorems"
  shows "caie_CEV_derivable \<Gamma> caie_appendix_C_axiom_package A"
  using assms
  by (auto simp: caie_appendix_C_theorems_def
      intro: caie_CEV_derivable_Thm32_from_axiom_package
        caie_CEV_derivable_Thm33_from_axiom_package
        caie_CEV_derivable_Thm34_from_axiom_package
        caie_CEV_derivable_Thm35_from_axiom_package
        caie_CEV_derivable_Thm36_from_axiom_package
        caie_CEV_derivable_Thm37_from_axiom_package
        caie_CEV_derivable_Thm38_from_axiom_package
        caie_CEV_derivable_Thm39_from_axiom_package
        caie_CEV_derivable_Thm40_from_axiom_package)


subsection \<open>Residual targets from bridge sources\<close>

text \<open>
  This layer records the precise bridge source for each Appendix C residual
  target.  The source side is either a package member or, in the first two
  cases, a conjunction already derivable from package members.  The bridge
  implication side is proved in CEV, using the definitional conversion facts
  and the Caie-specific pointwise principles above.
\<close>

definition caie_appendix_C_residual_bridge_pairs :: "(oterm * oterm) list" where
  "caie_appendix_C_residual_bridge_pairs =
    [(caie_name_expanded_down_phae_principle, caie_Thm32),
     (caie_Thm33_component_principles, caie_Thm33),
     (caie_phae_up_down_pointwise_principle, caie_Thm34),
     (caie_name_down_up_pointwise_principle, caie_Thm35),
     (caie_haecceity_up_extensionality_principle, caie_Thm36),
     (caie_phae_up_hae_witness_principle, caie_Thm37),
     (caie_wname_dsim_surrogacy_principle, caie_Thm38),
     (caie_hae_wname_dsim_identity_surrogacy_principle, caie_Thm39),
     (caie_wname_unique_name_down_eq_surrogacy_principle, caie_Thm40)]"

lemma caie_appendix_C_residual_bridge_targets:
  "set (map snd caie_appendix_C_residual_bridge_pairs) =
    set caie_appendix_C_theorems"
  by (simp add: caie_appendix_C_residual_bridge_pairs_def
      caie_appendix_C_theorems_def)

lemma caie_appendix_C_residual_bridge_targetD:
  assumes "A \<in> set caie_appendix_C_theorems"
  obtains S where "(S, A) \<in> set caie_appendix_C_residual_bridge_pairs"
proof -
  have cases:
      "A = caie_Thm32 \<or> A = caie_Thm33 \<or> A = caie_Thm34 \<or>
       A = caie_Thm35 \<or> A = caie_Thm36 \<or> A = caie_Thm37 \<or>
       A = caie_Thm38 \<or> A = caie_Thm39 \<or> A = caie_Thm40"
    using assms by (simp add: caie_appendix_C_theorems_def)
  then show ?thesis
  proof (elim disjE)
    assume A: "A = caie_Thm32"
    show ?thesis
      using that[of caie_name_expanded_down_phae_principle] A
      by (simp add: caie_appendix_C_residual_bridge_pairs_def)
  next
    assume A: "A = caie_Thm33"
    show ?thesis
      using that[of caie_Thm33_component_principles] A
      by (simp add: caie_appendix_C_residual_bridge_pairs_def)
  next
    assume A: "A = caie_Thm34"
    show ?thesis
      using that[of caie_phae_up_down_pointwise_principle] A
      by (simp add: caie_appendix_C_residual_bridge_pairs_def)
  next
    assume A: "A = caie_Thm35"
    show ?thesis
      using that[of caie_name_down_up_pointwise_principle] A
      by (simp add: caie_appendix_C_residual_bridge_pairs_def)
  next
    assume A: "A = caie_Thm36"
    show ?thesis
      using that[of caie_haecceity_up_extensionality_principle] A
      by (simp add: caie_appendix_C_residual_bridge_pairs_def)
  next
    assume A: "A = caie_Thm37"
    show ?thesis
      using that[of caie_phae_up_hae_witness_principle] A
      by (simp add: caie_appendix_C_residual_bridge_pairs_def)
  next
    assume A: "A = caie_Thm38"
    show ?thesis
      using that[of caie_wname_dsim_surrogacy_principle] A
      by (simp add: caie_appendix_C_residual_bridge_pairs_def)
  next
    assume A: "A = caie_Thm39"
    show ?thesis
      using that[of caie_hae_wname_dsim_identity_surrogacy_principle] A
      by (simp add: caie_appendix_C_residual_bridge_pairs_def)
  next
    assume A: "A = caie_Thm40"
    show ?thesis
      using that[of caie_wname_unique_name_down_eq_surrogacy_principle] A
      by (simp add: caie_appendix_C_residual_bridge_pairs_def)
  qed
qed

lemma typed_caie_appendix_C_residual_bridge_source:
  assumes "(S, A) \<in> set caie_appendix_C_residual_bridge_pairs"
  shows "\<Gamma> \<turnstile> S : Prop"
  using assms
  by (auto simp: caie_appendix_C_residual_bridge_pairs_def
      intro: typed_caie_name_expanded_down_phae_principle
        typed_caie_Thm33_component_principles
        typed_caie_phae_up_down_pointwise_principle
        typed_caie_name_down_up_pointwise_principle
        typed_caie_haecceity_up_extensionality_principle
        typed_caie_phae_up_hae_witness_principle
        typed_caie_wname_dsim_surrogacy_principle
        typed_caie_hae_wname_dsim_identity_surrogacy_principle
        typed_caie_wname_unique_name_down_eq_surrogacy_principle)

lemma typed_caie_appendix_C_residual_bridge_target:
  assumes "(S, A) \<in> set caie_appendix_C_residual_bridge_pairs"
  shows "\<Gamma> \<turnstile> A : Prop"
  using assms
  by (auto simp: caie_appendix_C_residual_bridge_pairs_def
      intro: typed_caie_Thm32 typed_caie_Thm33 typed_caie_Thm34
        typed_caie_Thm35 typed_caie_Thm36 typed_caie_Thm37
        typed_caie_Thm38 typed_caie_Thm39 typed_caie_Thm40)

lemma caie_CEV_derivable_residual_bridge_pair_imp:
  assumes "(S, A) \<in> set caie_appendix_C_residual_bridge_pairs"
  shows "caie_CEV_derivable \<Gamma> \<Delta> (Imp S A)"
proof -
  have cases:
      "(S = caie_name_expanded_down_phae_principle \<and> A = caie_Thm32) \<or>
       (S = caie_Thm33_component_principles \<and> A = caie_Thm33) \<or>
       (S = caie_phae_up_down_pointwise_principle \<and> A = caie_Thm34) \<or>
       (S = caie_name_down_up_pointwise_principle \<and> A = caie_Thm35) \<or>
       (S = caie_haecceity_up_extensionality_principle \<and> A = caie_Thm36) \<or>
       (S = caie_phae_up_hae_witness_principle \<and> A = caie_Thm37) \<or>
       (S = caie_wname_dsim_surrogacy_principle \<and> A = caie_Thm38) \<or>
       (S = caie_hae_wname_dsim_identity_surrogacy_principle \<and> A = caie_Thm39) \<or>
       (S = caie_wname_unique_name_down_eq_surrogacy_principle \<and>
        A = caie_Thm40)"
    using assms
    by (simp add: caie_appendix_C_residual_bridge_pairs_def)
  from cases show ?thesis
  proof (elim disjE conjE)
    assume S: "S = caie_name_expanded_down_phae_principle"
      and A: "A = caie_Thm32"
    have "\<Gamma> \<turnstile>\<^sub>CEV Imp S A"
      using CEV_caie_Thm32_of_expanded S A by simp
    then show ?thesis by (rule caie_CEV_derivable_of_theorem)
  next
    assume S: "S = caie_Thm33_component_principles"
      and A: "A = caie_Thm33"
    have "\<Gamma> \<turnstile>\<^sub>CEV Imp S A"
      using CEV_caie_Thm33_from_component_principles S A by simp
    then show ?thesis by (rule caie_CEV_derivable_of_theorem)
  next
    assume S: "S = caie_phae_up_down_pointwise_principle"
      and A: "A = caie_Thm34"
    have "\<Gamma> \<turnstile>\<^sub>CEV Imp S A"
      using CEV_caie_Thm34_from_up_down_pointwise S A by simp
    then show ?thesis by (rule caie_CEV_derivable_of_theorem)
  next
    assume S: "S = caie_name_down_up_pointwise_principle"
      and A: "A = caie_Thm35"
    have "\<Gamma> \<turnstile>\<^sub>CEV Imp S A"
      using CEV_caie_Thm35_from_down_up_pointwise S A by simp
    then show ?thesis by (rule caie_CEV_derivable_of_theorem)
  next
    assume S: "S = caie_haecceity_up_extensionality_principle"
      and A: "A = caie_Thm36"
    have "\<Gamma> \<turnstile>\<^sub>CEV Imp S A"
      using CEV_caie_Thm36_from_haecceity_up_extensionality S A by simp
    then show ?thesis by (rule caie_CEV_derivable_of_theorem)
  next
    assume S: "S = caie_phae_up_hae_witness_principle"
      and A: "A = caie_Thm37"
    have "\<Gamma> \<turnstile>\<^sub>CEV Imp S A"
      using CEV_caie_Thm37_from_up_hae_witness S A by simp
    then show ?thesis by (rule caie_CEV_derivable_of_theorem)
  next
    assume S: "S = caie_wname_dsim_surrogacy_principle"
      and A: "A = caie_Thm38"
    have "\<Gamma> \<turnstile>\<^sub>CEV Imp S A"
      using CEV_caie_Thm38_from_wname_dsim_surrogacy S A by simp
    then show ?thesis by (rule caie_CEV_derivable_of_theorem)
  next
    assume S: "S = caie_hae_wname_dsim_identity_surrogacy_principle"
      and A: "A = caie_Thm39"
    have "\<Gamma> \<turnstile>\<^sub>CEV Imp S A"
      using CEV_caie_Thm39_from_hae_wname_dsim_identity_surrogacy S A by simp
    then show ?thesis by (rule caie_CEV_derivable_of_theorem)
  next
    assume S: "S = caie_wname_unique_name_down_eq_surrogacy_principle"
      and A: "A = caie_Thm40"
    have "\<Gamma> \<turnstile>\<^sub>CEV Imp S A"
      using CEV_caie_Thm40_of_down_eq_surrogacy S A by simp
    then show ?thesis by (rule caie_CEV_derivable_of_theorem)
  qed
qed

lemma caie_appendix_C_axiom_package_derives_residual_bridge_source:
  assumes "(S, A) \<in> set caie_appendix_C_residual_bridge_pairs"
  shows "caie_CEV_derivable \<Gamma> caie_appendix_C_axiom_package S"
proof -
  have cases:
      "(S = caie_name_expanded_down_phae_principle \<and> A = caie_Thm32) \<or>
       (S = caie_Thm33_component_principles \<and> A = caie_Thm33) \<or>
       (S = caie_phae_up_down_pointwise_principle \<and> A = caie_Thm34) \<or>
       (S = caie_name_down_up_pointwise_principle \<and> A = caie_Thm35) \<or>
       (S = caie_haecceity_up_extensionality_principle \<and> A = caie_Thm36) \<or>
       (S = caie_phae_up_hae_witness_principle \<and> A = caie_Thm37) \<or>
       (S = caie_wname_dsim_surrogacy_principle \<and> A = caie_Thm38) \<or>
       (S = caie_hae_wname_dsim_identity_surrogacy_principle \<and> A = caie_Thm39) \<or>
       (S = caie_wname_unique_name_down_eq_surrogacy_principle \<and>
        A = caie_Thm40)"
    using assms
    by (simp add: caie_appendix_C_residual_bridge_pairs_def)
  from cases show ?thesis
  proof (elim disjE conjE)
    assume S: "S = caie_name_expanded_down_phae_principle"
      and A: "A = caie_Thm32"
    then show ?thesis
      using caie_CEV_derivable_name_expanded_down_phae_from_axiom_package
      by simp
  next
    assume S: "S = caie_Thm33_component_principles"
      and A: "A = caie_Thm33"
    then show ?thesis
      using caie_CEV_derivable_Thm33_component_principles_from_axiom_package
      by simp
  next
    assume S: "S = caie_phae_up_down_pointwise_principle"
      and A: "A = caie_Thm34"
    have "caie_phae_up_down_pointwise_principle \<in>
        set caie_name_haecceity_principles"
      by (simp add: caie_name_haecceity_principles_def)
    then have "caie_CEV_derivable \<Gamma> caie_appendix_C_axiom_package
        caie_phae_up_down_pointwise_principle"
      by (rule caie_CEV_derivable_name_haecceity_axiom)
    then show ?thesis using S by simp
  next
    assume S: "S = caie_name_down_up_pointwise_principle"
      and A: "A = caie_Thm35"
    have "caie_name_down_up_pointwise_principle \<in>
        set caie_name_haecceity_principles"
      by (simp add: caie_name_haecceity_principles_def)
    then have "caie_CEV_derivable \<Gamma> caie_appendix_C_axiom_package
        caie_name_down_up_pointwise_principle"
      by (rule caie_CEV_derivable_name_haecceity_axiom)
    then show ?thesis using S by simp
  next
    assume S: "S = caie_haecceity_up_extensionality_principle"
      and A: "A = caie_Thm36"
    have "caie_haecceity_up_extensionality_principle \<in>
        set caie_name_haecceity_principles"
      by (simp add: caie_name_haecceity_principles_def)
    then have "caie_CEV_derivable \<Gamma> caie_appendix_C_axiom_package
        caie_haecceity_up_extensionality_principle"
      by (rule caie_CEV_derivable_name_haecceity_axiom)
    then show ?thesis using S by simp
  next
    assume S: "S = caie_phae_up_hae_witness_principle"
      and A: "A = caie_Thm37"
    have "caie_phae_up_hae_witness_principle \<in>
        set caie_name_haecceity_principles"
      by (simp add: caie_name_haecceity_principles_def)
    then have "caie_CEV_derivable \<Gamma> caie_appendix_C_axiom_package
        caie_phae_up_hae_witness_principle"
      by (rule caie_CEV_derivable_name_haecceity_axiom)
    then show ?thesis using S by simp
  next
    assume S: "S = caie_wname_dsim_surrogacy_principle"
      and A: "A = caie_Thm38"
    have "caie_wname_dsim_surrogacy_principle \<in>
        set caie_name_haecceity_principles"
      by (simp add: caie_name_haecceity_principles_def)
    then have "caie_CEV_derivable \<Gamma> caie_appendix_C_axiom_package
        caie_wname_dsim_surrogacy_principle"
      by (rule caie_CEV_derivable_name_haecceity_axiom)
    then show ?thesis using S by simp
  next
    assume S: "S = caie_hae_wname_dsim_identity_surrogacy_principle"
      and A: "A = caie_Thm39"
    have "caie_hae_wname_dsim_identity_surrogacy_principle \<in>
        set caie_name_haecceity_principles"
      by (simp add: caie_name_haecceity_principles_def)
    then have "caie_CEV_derivable \<Gamma> caie_appendix_C_axiom_package
        caie_hae_wname_dsim_identity_surrogacy_principle"
      by (rule caie_CEV_derivable_name_haecceity_axiom)
    then show ?thesis using S by simp
  next
    assume S: "S = caie_wname_unique_name_down_eq_surrogacy_principle"
      and A: "A = caie_Thm40"
    have "caie_wname_unique_name_down_eq_surrogacy_principle \<in>
        set caie_name_haecceity_principles"
      by (simp add: caie_name_haecceity_principles_def)
    then have "caie_CEV_derivable \<Gamma> caie_appendix_C_axiom_package
        caie_wname_unique_name_down_eq_surrogacy_principle"
      by (rule caie_CEV_derivable_name_haecceity_axiom)
    then show ?thesis using S by simp
  qed
qed

lemma caie_appendix_C_axiom_package_derives_residual_bridge_target:
  assumes "(S, A) \<in> set caie_appendix_C_residual_bridge_pairs"
  shows "caie_CEV_derivable \<Gamma> caie_appendix_C_axiom_package A"
proof -
  have d_source: "caie_CEV_derivable \<Gamma> caie_appendix_C_axiom_package S"
    using assms by (rule caie_appendix_C_axiom_package_derives_residual_bridge_source)
  have d_bridge: "caie_CEV_derivable \<Gamma> caie_appendix_C_axiom_package (Imp S A)"
    using assms by (rule caie_CEV_derivable_residual_bridge_pair_imp)
  show ?thesis
    using d_source d_bridge by (rule caie_CEV_derivable.caie_MP)
qed

lemma caie_appendix_C_residual_target_from_axiom_package_using_bridge_pairs:
  assumes "A \<in> set caie_appendix_C_theorems"
  shows "caie_CEV_derivable \<Gamma> caie_appendix_C_axiom_package A"
proof -
  from assms obtain S
    where pair: "(S, A) \<in> set caie_appendix_C_residual_bridge_pairs"
    by (rule caie_appendix_C_residual_bridge_targetD)
  then show ?thesis
    by (rule caie_appendix_C_axiom_package_derives_residual_bridge_target)
qed


subsection \<open>Current Appendix C dependency sorting\<close>

text \<open>
  The verified definitional material consists of beta-eta bridges available
  inside arbitrary Caie assumption contexts.  These bridges are the reusable
  definitional facts for later Appendix C derivations; none of the full
  Appendix C target statements 32--40 is currently classified as following
  from definition and beta-eta conversion alone.  The explicit axiom package
  now derives Theorems 32--40 through the residual derivation layer above.
  The equality and haecceity cases use CEV's proved contextual unary
  equivalence rule; no extra contextual-equivalence assumption is made.
  Theorem 37 uses the beta-eta bridge for the upward operator together with
  the package's smaller possible-haecceity witness principle.  Theorem 38 uses the
  down-similarity beta-eta bridge to convert the package's expanded
  down-projection surrogacy principle into Caie's displayed statement.
  Theorem 39 uses the same down-similarity bridge to convert an expanded
  haecceity/weak-name identity surrogate into the official down-similarity
  biconditional.  Theorem 40 uses the same bridge under existential and
  universal formula contexts to convert an expanded unique-name surrogate into
  Caie's displayed uniqueness statement.
\<close>

definition caie_appendix_C_definitional_targets :: "oterm list" where
  "caie_appendix_C_definitional_targets = []"

definition caie_appendix_C_principle_targets :: "oterm list" where
  "caie_appendix_C_principle_targets = caie_appendix_C_theorems"

lemma caie_appendix_C_current_sort:
  "caie_appendix_C_definitional_targets = [] \<and>
   caie_appendix_C_principle_targets = caie_appendix_C_theorems"
  by (simp add: caie_appendix_C_definitional_targets_def
      caie_appendix_C_principle_targets_def)

lemma caie_appendix_C_sort_covers:
  "set caie_appendix_C_theorems =
    set caie_appendix_C_definitional_targets \<union>
    set caie_appendix_C_principle_targets"
  by (simp add: caie_appendix_C_definitional_targets_def
      caie_appendix_C_principle_targets_def)

lemma caie_appendix_C_sort_disjoint:
  "set caie_appendix_C_definitional_targets \<inter>
    set caie_appendix_C_principle_targets = {}"
  by (simp add: caie_appendix_C_definitional_targets_def)

lemma caie_CEV_derivable_definitional_target:
  assumes "A \<in> set caie_appendix_C_definitional_targets"
  shows "caie_CEV_derivable \<Gamma> \<Delta> A"
  using assms
  by (simp add: caie_appendix_C_definitional_targets_def)

lemma typed_caie_appendix_C_principle_target:
  assumes "A \<in> set caie_appendix_C_principle_targets"
  shows "\<Gamma> \<turnstile> A : Prop"
  using assms
  unfolding caie_appendix_C_principle_targets_def
  by (rule typed_caie_appendix_C_theorem)

lemma caie_appendix_C_principle_assumption_package:
  "caie_assumption_package \<Gamma> caie_appendix_C_principle_targets"
  unfolding caie_assumption_package_def
  by (auto intro: typed_caie_appendix_C_principle_target)

lemma caie_CEV_derivable_principle_target_assumption:
  assumes "A \<in> set caie_appendix_C_principle_targets"
  shows "caie_CEV_derivable \<Gamma> caie_appendix_C_principle_targets A"
  using caie_appendix_C_principle_assumption_package assms
  by (rule caie_CEV_derivable_assumption)

lemma caie_appendix_C_principle_target_from_axiom_package_using_bridges:
  assumes "A \<in> set caie_appendix_C_principle_targets"
  shows "caie_CEV_derivable \<Gamma> caie_appendix_C_axiom_package A"
  using assms
  unfolding caie_appendix_C_principle_targets_def
  by (rule caie_appendix_C_residual_target_from_axiom_package_using_bridge_pairs)

definition caie_appendix_C_axiom_package_verified_targets :: "oterm list" where
  "caie_appendix_C_axiom_package_verified_targets =
    [caie_Thm32, caie_Thm33, caie_Thm34, caie_Thm35, caie_Thm36,
     caie_Thm37, caie_Thm38, caie_Thm39, caie_Thm40]"

definition caie_appendix_C_axiom_package_remaining_targets :: "oterm list" where
  "caie_appendix_C_axiom_package_remaining_targets =
    []"

lemma caie_appendix_C_axiom_package_target_sort_covers:
  "set caie_appendix_C_principle_targets =
    set caie_appendix_C_axiom_package_verified_targets \<union>
    set caie_appendix_C_axiom_package_remaining_targets"
  by (auto simp: caie_appendix_C_principle_targets_def
      caie_appendix_C_theorems_def
      caie_appendix_C_axiom_package_verified_targets_def
      caie_appendix_C_axiom_package_remaining_targets_def)

lemma caie_appendix_C_axiom_package_target_sort_disjoint:
  "set caie_appendix_C_axiom_package_verified_targets \<inter>
    set caie_appendix_C_axiom_package_remaining_targets = {}"
  by (simp add: caie_appendix_C_axiom_package_verified_targets_def
      caie_appendix_C_axiom_package_remaining_targets_def
      caie_Thm32_def caie_Thm33_def caie_Thm34_def caie_Thm35_def
      caie_Thm36_def caie_Thm37_def caie_Thm38_def caie_Thm39_def
      caie_Thm40_def caie_term_defs caie_type_defs)

lemma typed_caie_appendix_C_axiom_package_verified_target:
  assumes "A \<in> set caie_appendix_C_axiom_package_verified_targets"
  shows "\<Gamma> \<turnstile> A : Prop"
  using assms
  by (auto simp: caie_appendix_C_axiom_package_verified_targets_def
      intro: typed_caie_Thm32 typed_caie_Thm33 typed_caie_Thm34
        typed_caie_Thm35 typed_caie_Thm36 typed_caie_Thm37
        typed_caie_Thm38 typed_caie_Thm39 typed_caie_Thm40)

lemma typed_caie_appendix_C_axiom_package_remaining_target:
  assumes "A \<in> set caie_appendix_C_axiom_package_remaining_targets"
  shows "\<Gamma> \<turnstile> A : Prop"
  using assms
  by (auto simp: caie_appendix_C_axiom_package_remaining_targets_def
      intro: typed_caie_Thm40)

lemma caie_appendix_C_axiom_package_derives_verified_target:
  assumes "A \<in> set caie_appendix_C_axiom_package_verified_targets"
  shows "caie_CEV_derivable \<Gamma> caie_appendix_C_axiom_package A"
  using assms
  by (auto simp: caie_appendix_C_axiom_package_verified_targets_def
      intro: caie_CEV_derivable_Thm32_from_axiom_package
        caie_CEV_derivable_Thm33_from_axiom_package
        caie_CEV_derivable_Thm34_from_axiom_package
        caie_CEV_derivable_Thm35_from_axiom_package
        caie_CEV_derivable_Thm36_from_axiom_package
        caie_CEV_derivable_Thm37_from_axiom_package
        caie_CEV_derivable_Thm38_from_axiom_package
        caie_CEV_derivable_Thm39_from_axiom_package
        caie_CEV_derivable_Thm40_from_axiom_package)

definition caie_appendix_C_axiom_package_closes_targets :: "ctx \<Rightarrow> bool" where
  "caie_appendix_C_axiom_package_closes_targets \<Gamma> \<longleftrightarrow>
    (\<forall>A \<in> set caie_appendix_C_principle_targets.
      caie_CEV_derivable \<Gamma> caie_appendix_C_axiom_package A)"

lemma caie_appendix_C_axiom_package_closes_targetD:
  assumes "caie_appendix_C_axiom_package_closes_targets \<Gamma>"
    and "A \<in> set caie_appendix_C_principle_targets"
  shows "caie_CEV_derivable \<Gamma> caie_appendix_C_axiom_package A"
  using assms
  by (simp add: caie_appendix_C_axiom_package_closes_targets_def)

lemma caie_appendix_C_axiom_package_closes_targets_from_residual_bridges:
  "caie_appendix_C_axiom_package_closes_targets \<Gamma>"
proof (unfold caie_appendix_C_axiom_package_closes_targets_def, intro ballI)
  fix A
  assume "A \<in> set caie_appendix_C_principle_targets"
  then show "caie_CEV_derivable \<Gamma> caie_appendix_C_axiom_package A"
    by (rule caie_appendix_C_principle_target_from_axiom_package_using_bridges)
qed

lemma caie_appendix_C_axiom_package_closes_targets_from_verified:
  "caie_appendix_C_axiom_package_closes_targets \<Gamma>"
proof (unfold caie_appendix_C_axiom_package_closes_targets_def, intro ballI)
  fix A
  assume A_in: "A \<in> set caie_appendix_C_principle_targets"
  have A_verified: "A \<in> set caie_appendix_C_axiom_package_verified_targets"
    using A_in
    by (auto simp: caie_appendix_C_principle_targets_def
        caie_appendix_C_theorems_def
        caie_appendix_C_axiom_package_verified_targets_def)
  show "caie_CEV_derivable \<Gamma> caie_appendix_C_axiom_package A"
    using A_verified
    by (rule caie_appendix_C_axiom_package_derives_verified_target)
qed

end
