theory Bacon_Caie_Mstar
  imports Main
begin

section \<open>Caie's finite model M*\<close>

text \<open>
  This theory records the finite semantic model from Caie's Appendix B,
  Definition 28, and verifies the concrete model claims from Proposition 29
  that are independent of the deep Bacon syntax: the classifier P* is a Name,
  P* is empty, and the two displayed Name classifiers cover the actual and
  merely possible individuals.
\<close>

datatype world = At | Wv
datatype ind = Ia | Ip

fun acc :: "world \<Rightarrow> world \<Rightarrow> bool" where
  "acc At At = True"
| "acc At Wv = True"
| "acc Wv At = False"
| "acc Wv Wv = True"

definition accs :: "world \<Rightarrow> world set" where
  "accs w = {v. acc w v}"

lemma accs_At[simp, code]: "accs At = {At, Wv}"
  by (auto simp: accs_def) (metis acc.simps world.exhaust)

lemma accs_Wv[simp, code]: "accs Wv = {Wv}"
  by (auto simp: accs_def) (metis acc.simps world.exhaust)

fun De :: "world \<Rightarrow> ind set" where
  "De At = {Ia}"
| "De Wv = {Ia, Ip}"

datatype etl =
    E1 | E2 | E3 | E4 | E5 | E6 | E7 | E8
  | V1 | V2 | V3 | V4

type_synonym classifier = "world \<Rightarrow> etl \<Rightarrow> world set"
type_synonym classifier_class = "world \<Rightarrow> classifier \<Rightarrow> bool"

fun etv :: "etl \<Rightarrow> world \<Rightarrow> ind \<Rightarrow> world set" where
  "etv E1 At Ia = {At, Wv}"
| "etv E1 Wv Ia = {Wv}"
| "etv E1 Wv Ip = {Wv}"
| "etv E2 At Ia = {At, Wv}"
| "etv E2 Wv Ia = {Wv}"
| "etv E3 At Ia = {Wv}"
| "etv E3 Wv Ia = {Wv}"
| "etv E3 Wv Ip = {Wv}"
| "etv E4 At Ia = {Wv}"
| "etv E4 Wv Ia = {Wv}"
| "etv E5 At Ia = {At}"
| "etv E5 Wv Ip = {Wv}"
| "etv E6 At Ia = {At}"
| "etv E7 Wv Ip = {Wv}"
| "etv V1 Wv Ia = {Wv}"
| "etv V1 Wv Ip = {Wv}"
| "etv V2 Wv Ia = {Wv}"
| "etv V3 Wv Ip = {Wv}"
| "etv _ _ _ = {}"

fun Det :: "world \<Rightarrow> etl set" where
  "Det At = {E1, E2, E3, E4, E5, E6, E7, E8}"
| "Det Wv = {V1, V2, V3, V4}"

fun haec :: "world \<Rightarrow> ind \<Rightarrow> etl" where
  "haec At Ia = E2"
| "haec Wv Ia = V2"
| "haec Wv Ip = V3"
| "haec _ _ = E8"

fun negp :: "world \<Rightarrow> etl \<Rightarrow> etl" where
  "negp At E1 = E8"
| "negp At E2 = E7"
| "negp At E3 = E6"
| "negp At E4 = E5"
| "negp At E5 = E4"
| "negp At E6 = E3"
| "negp At E7 = E2"
| "negp At E8 = E1"
| "negp Wv V1 = V4"
| "negp Wv V2 = V3"
| "negp Wv V3 = V2"
| "negp Wv V4 = V1"
| "negp _ _ = E8"

fun bott :: "world \<Rightarrow> etl" where
  "bott At = E8"
| "bott Wv = V4"

fun Astar :: "world \<Rightarrow> etl \<Rightarrow> world set" where
  "Astar At E1 = {At, Wv}"
| "Astar At E2 = {At, Wv}"
| "Astar At E3 = {Wv}"
| "Astar At E4 = {Wv}"
| "Astar At E5 = {At}"
| "Astar At E6 = {At}"
| "Astar Wv V1 = {Wv}"
| "Astar Wv V2 = {Wv}"
| "Astar _ _ = {}"

fun Pstar :: "world \<Rightarrow> etl \<Rightarrow> world set" where
  "Pstar At E1 = {At, Wv}"
| "Pstar At E3 = {At, Wv}"
| "Pstar At E5 = {At, Wv}"
| "Pstar At E7 = {At, Wv}"
| "Pstar Wv V1 = {Wv}"
| "Pstar Wv V3 = {Wv}"
| "Pstar _ _ = {}"

lemma haec_correct:
  assumes "acc w v" "d \<in> De v" "x \<in> De w"
  shows "etv (haec w x) v d = (if d = x then accs v else {})"
  using assms by (cases w; cases v; cases d; cases x) auto

lemma negp_correct:
  assumes "acc w v" "d \<in> De v" "e \<in> Det w"
  shows "etv (negp w e) v d = accs v - etv e v d"
  using assms by (cases w; cases v; cases e; cases d) auto

definition papp :: "etl \<Rightarrow> world \<Rightarrow> ind \<Rightarrow> bool" where
  "papp e w d \<longleftrightarrow> w \<in> etv e w d"

definition capp :: "(world \<Rightarrow> etl \<Rightarrow> world set) \<Rightarrow> world \<Rightarrow> etl \<Rightarrow> bool" where
  "capp Q w e \<longleftrightarrow> w \<in> Q w e"

definition comp_at :: "(world \<Rightarrow> etl \<Rightarrow> world set) \<Rightarrow> world \<Rightarrow> bool" where
  "comp_at Q w \<longleftrightarrow> (\<forall>P1\<in>Det w. capp Q w P1 \<or> capp Q w (negp w P1))"

definition cons_at :: "(world \<Rightarrow> etl \<Rightarrow> world set) \<Rightarrow> world \<Rightarrow> bool" where
  "cons_at Q w \<longleftrightarrow> \<not> capp Q w (bott w)"

definition ns_at :: "(world \<Rightarrow> etl \<Rightarrow> world set) \<Rightarrow> world \<Rightarrow> bool" where
  "ns_at Q w \<longleftrightarrow> (\<forall>P1\<in>Det w. (\<not> capp Q w P1) = capp Q w (negp w P1))"

definition ac_at :: "(world \<Rightarrow> etl \<Rightarrow> world set) \<Rightarrow> world \<Rightarrow> bool" where
  "ac_at Q w \<longleftrightarrow>
    (\<forall>x\<in>De w. capp Q w (haec w x) \<longrightarrow>
      (\<forall>P1\<in>Det w. capp Q w P1 = papp P1 w x))"

definition hp_at :: "(world \<Rightarrow> etl \<Rightarrow> world set) \<Rightarrow> world \<Rightarrow> bool" where
  "hp_at Q w \<longleftrightarrow>
    (\<forall>x\<in>De w. capp Q w (haec w x) \<longrightarrow>
      (\<forall>v\<in>accs w. capp Q v (haec v x)))"

definition nhp_at :: "(world \<Rightarrow> etl \<Rightarrow> world set) \<Rightarrow> world \<Rightarrow> bool" where
  "nhp_at Q w \<longleftrightarrow>
    (\<forall>x\<in>De w. \<not> capp Q w (haec w x) \<longrightarrow>
      (\<forall>v\<in>accs w. \<not> capp Q v (haec v x)))"

named_theorems mstar_defs
declare papp_def[mstar_defs] capp_def[mstar_defs] comp_at_def[mstar_defs]
  cons_at_def[mstar_defs] ns_at_def[mstar_defs] ac_at_def[mstar_defs]
  hp_at_def[mstar_defs] nhp_at_def[mstar_defs]

theorem Pstar_basic_name_conditions:
  "comp_at Pstar w \<and> cons_at Pstar w \<and> ns_at Pstar w \<and>
   ac_at Pstar w \<and> hp_at Pstar w \<and> nhp_at Pstar w"
  by (cases w) (simp_all add: mstar_defs)

theorem Astar_basic_name_conditions:
  "comp_at Astar w \<and> cons_at Astar w \<and> ns_at Astar w \<and>
   ac_at Astar w \<and> hp_at Astar w \<and> nhp_at Astar w"
  by (cases w) (simp_all add: mstar_defs)

fun cpet :: "world \<Rightarrow> world \<Rightarrow> etl \<Rightarrow> etl" where
  "cpet At Wv E1 = V1"
| "cpet At Wv E2 = V2"
| "cpet At Wv E3 = V1"
| "cpet At Wv E4 = V2"
| "cpet At Wv E5 = V3"
| "cpet At Wv E6 = V4"
| "cpet At Wv E7 = V3"
| "cpet At Wv E8 = V4"
| "cpet w v e = e"

lemma cpet_correct:
  assumes "e \<in> Det w" "acc w v" "acc v u" "d \<in> De u"
  shows "etv (cpet w v e) u d = etv e u d"
  using assms by (cases w; cases v; cases e; cases u; cases d) auto

definition ent :: "world \<Rightarrow> etl \<Rightarrow> etl \<Rightarrow> bool" where
  "ent w P1 P2 \<longleftrightarrow>
    (\<forall>v\<in>accs w. \<forall>d\<in>De v. papp P1 v d \<longrightarrow> papp P2 v d)"

definition uc_at :: "(world \<Rightarrow> etl \<Rightarrow> world set) \<Rightarrow> world \<Rightarrow> bool" where
  "uc_at Q w \<longleftrightarrow>
    (\<forall>P1\<in>Det w. \<forall>P2\<in>Det w.
      (capp Q w P1 \<and> ent w P1 P2) \<longrightarrow> capp Q w P2)"

theorem Pstar_UC: "uc_at Pstar w"
  by (cases w) (simp_all add: uc_at_def ent_def mstar_defs)

theorem Astar_UC: "uc_at Astar w"
  by (cases w) (simp_all add: uc_at_def ent_def mstar_defs)

definition closest :: "world \<Rightarrow> (world \<Rightarrow> bool) \<Rightarrow> world" where
  "closest w phi = (if w = At \<and> phi At then At else Wv)"

definition cf_at :: "world \<Rightarrow> (world \<Rightarrow> bool) \<Rightarrow> (world \<Rightarrow> bool) \<Rightarrow> bool" where
  "cf_at w phi psi \<longleftrightarrow>
    (if (\<exists>v\<in>accs w. phi v) then psi (closest w phi) else True)"

definition acf_at :: "(world \<Rightarrow> etl \<Rightarrow> world set) \<Rightarrow> world \<Rightarrow> bool" where
  "acf_at Q w \<longleftrightarrow>
    (\<forall>P1\<in>Det w.
      capp Q w P1 =
        cf_at w
          (\<lambda>v. \<exists>x\<in>De v. capp Q v (haec v x))
          (\<lambda>v. capp Q v (cpet w v P1)))"

theorem Pstar_ACF: "acf_at Pstar w"
  by (cases w) (simp_all add: acf_at_def cf_at_def closest_def mstar_defs)

theorem Astar_ACF: "acf_at Astar w"
  by (cases w) (simp_all add: acf_at_def cf_at_def closest_def mstar_defs)

definition is_glb :: "world \<Rightarrow> etl set \<Rightarrow> etl \<Rightarrow> bool" where
  "is_glb w S P1 \<longleftrightarrow>
    (\<forall>P2\<in>S. ent w P1 P2) \<and>
    (\<forall>P3\<in>Det w. (\<forall>P2\<in>S. ent w P3 P2) \<longrightarrow> ent w P3 P1)"

definition glbc_at :: "(world \<Rightarrow> etl \<Rightarrow> world set) \<Rightarrow> world \<Rightarrow> bool" where
  "glbc_at Q w \<longleftrightarrow>
    (\<forall>S\<subseteq>Det w. (\<forall>P1\<in>S. capp Q w P1) \<longrightarrow>
      (\<forall>P1\<in>Det w. is_glb w S P1 \<longrightarrow> capp Q w P1))"

fun det_list :: "world \<Rightarrow> etl list" where
  "det_list At = [E1, E2, E3, E4, E5, E6, E7, E8]"
| "det_list Wv = [V1, V2, V3, V4]"

lemma Det_set: "Det w = set (det_list w)"
  by (cases w) auto

lemma ball_subset_subseqs:
  "(\<forall>S. S \<subseteq> set xs \<longrightarrow> P S) =
   (\<forall>ys \<in> set (subseqs xs). P (set ys))"
proof
  assume all_subsets: "\<forall>S. S \<subseteq> set xs \<longrightarrow> P S"
  show "\<forall>ys \<in> set (subseqs xs). P (set ys)"
    using all_subsets subseqs_powset by (metis Pow_iff image_eqI)
next
  assume subseqs: "\<forall>ys \<in> set (subseqs xs). P (set ys)"
  show "\<forall>S. S \<subseteq> set xs \<longrightarrow> P S"
    using subseqs subset_subseqs by (metis image_iff)
qed

theorem Pstar_GLBC: "glbc_at Pstar w"
proof (cases w)
  case At
  have "glbc_at Pstar At"
    unfolding glbc_at_def Det_set by (subst ball_subset_subseqs) eval
  then show ?thesis
    using At by simp
next
  case Wv
  have "glbc_at Pstar Wv"
    unfolding glbc_at_def Det_set by (subst ball_subset_subseqs) eval
  then show ?thesis
    using Wv by simp
qed

theorem Astar_GLBC: "glbc_at Astar w"
proof (cases w)
  case At
  have "glbc_at Astar At"
    unfolding glbc_at_def Det_set by (subst ball_subset_subseqs) eval
  then show ?thesis
    using At by simp
next
  case Wv
  have "glbc_at Astar Wv"
    unfolding glbc_at_def Det_set by (subst ball_subset_subseqs) eval
  then show ?thesis
    using Wv by simp
qed

definition name_at :: "(world \<Rightarrow> etl \<Rightarrow> world set) \<Rightarrow> world \<Rightarrow> bool" where
  "name_at Q w \<longleftrightarrow>
    comp_at Q w \<and> cons_at Q w \<and> uc_at Q w \<and> glbc_at Q w \<and>
    ac_at Q w \<and> hp_at Q w \<and> nhp_at Q w \<and> acf_at Q w"

theorem Pstar_is_Name:
  "name_at Pstar w"
  unfolding name_at_def
  using Pstar_basic_name_conditions Pstar_UC Pstar_GLBC Pstar_ACF by blast

theorem Astar_is_Name:
  "name_at Astar w"
  unfolding name_at_def
  using Astar_basic_name_conditions Astar_UC Astar_GLBC Astar_ACF by blast

theorem bullet3_P_is_empty:
  "\<not> (\<exists>x \<in> De At. capp Pstar At (haec At x))"
  by (simp add: capp_def)

theorem Astar_nonempty:
  "\<exists>x \<in> De At. capp Astar At (haec At x)"
  by (simp add: capp_def)

definition classifier_agrees_on_domains :: "classifier \<Rightarrow> classifier \<Rightarrow> bool" where
  "classifier_agrees_on_domains Q R \<longleftrightarrow>
    (\<forall>w e. e \<in> Det w \<longrightarrow> capp Q w e = capp R w e)"

definition mstar_Name :: "classifier \<Rightarrow> bool" where
  "mstar_Name Q \<longleftrightarrow>
    classifier_agrees_on_domains Q Astar \<or>
    classifier_agrees_on_domains Q Pstar"

definition name_class :: classifier_class where
  "name_class w Q \<longleftrightarrow> mstar_Name Q"

definition persistent_class_at :: "classifier_class \<Rightarrow> world \<Rightarrow> bool" where
  "persistent_class_at N w \<longleftrightarrow>
    (\<forall>v\<in>accs w. \<forall>Q. N v Q \<longrightarrow> (\<forall>u\<in>accs v. N u Q))"

definition inextensible_class_at :: "classifier_class \<Rightarrow> world \<Rightarrow> bool" where
  "inextensible_class_at N w \<longleftrightarrow>
    (\<forall>v\<in>accs w. \<forall>X. (\<forall>Q. N v Q \<longrightarrow> (\<forall>u\<in>accs v. X u Q)) \<longrightarrow>
      (\<forall>u\<in>accs v. \<forall>Q. N u Q \<longrightarrow> X u Q))"

definition rigid_class_at :: "classifier_class \<Rightarrow> world \<Rightarrow> bool" where
  "rigid_class_at N w \<longleftrightarrow>
    persistent_class_at N w \<and> inextensible_class_at N w"

definition boxed_name_coverage_at :: "classifier_class \<Rightarrow> world \<Rightarrow> bool" where
  "boxed_name_coverage_at N w \<longleftrightarrow>
    (\<forall>v\<in>accs w. \<forall>x\<in>De v. \<exists>Q. N v Q \<and> capp Q v (haec v x))"

lemma mstar_Name_Astar[simp]: "mstar_Name Astar"
  by (simp add: mstar_Name_def classifier_agrees_on_domains_def)

lemma mstar_Name_Pstar[simp]: "mstar_Name Pstar"
  by (simp add: mstar_Name_def classifier_agrees_on_domains_def)

theorem name_class_is_rigid:
  "rigid_class_at name_class w"
  by (cases w)
    (auto simp: rigid_class_at_def persistent_class_at_def
      inextensible_class_at_def name_class_def)

theorem name_class_exact_for_mstar_Names:
  "name_class w Q \<longleftrightarrow> mstar_Name Q"
  by (simp add: name_class_def)

theorem name_class_contains_displayed_Names:
  "name_class w Astar \<and> name_class w Pstar"
  by (simp add: name_class_def)

theorem name_class_boxed_coverage:
  "boxed_name_coverage_at name_class w"
  by (cases w)
    (auto simp: boxed_name_coverage_at_def name_class_def mstar_Name_def
      classifier_agrees_on_domains_def capp_def)

theorem Mstar_name_plenitude_witness:
  "\<exists>N. rigid_class_at N At \<and>
    (\<forall>Q. mstar_Name Q \<longleftrightarrow> N At Q) \<and>
    boxed_name_coverage_at N At"
  using name_class_is_rigid name_class_boxed_coverage
  by (intro exI[of _ name_class]) (simp add: name_class_def)

theorem Mstar_name_coverage:
  assumes "x \<in> De w"
  shows "\<exists>Q. (Q = Astar \<or> Q = Pstar) \<and> name_at Q w \<and> capp Q w (haec w x)"
  using assms Astar_is_Name Pstar_is_Name
  by (cases w; cases x) (auto simp: capp_def)

subsection \<open>Abstract bridge for Proposition 29's background-logic bullet\<close>

text \<open>
  Proposition 29's first bullet is not a finite-table fact about @{term At},
  @{term Astar}, or @{term Pstar}.  It is the instance of Caie's general
  soundness result for NDS models: if a formula is a theorem of the background
  logic, then it is true in every NDS model, hence true in @{text "M*"} once
  @{text "M*"} has been shown to be an NDS model.  We record that dependency
  abstractly, with an arbitrary formula type and an arbitrary truth predicate,
  so the finite model file does not smuggle in Proposition 27.
\<close>

datatype mstar_model = Mstar_model

definition nds_background_soundness ::
  "('model \<Rightarrow> bool) \<Rightarrow> ('formula \<Rightarrow> bool) \<Rightarrow>
    ('model \<Rightarrow> 'formula \<Rightarrow> bool) \<Rightarrow> bool" where
  "nds_background_soundness is_NDS_model theorem_of_background true_in \<longleftrightarrow>
    (\<forall>M A. is_NDS_model M \<longrightarrow> theorem_of_background A \<longrightarrow> true_in M A)"

definition mstar_nds_model_obligation :: "(mstar_model \<Rightarrow> bool) \<Rightarrow> bool" where
  "mstar_nds_model_obligation is_NDS_model \<longleftrightarrow>
    is_NDS_model Mstar_model"

definition mstar_background_theorem_truth ::
  "('formula \<Rightarrow> bool) \<Rightarrow> (mstar_model \<Rightarrow> 'formula \<Rightarrow> bool) \<Rightarrow> bool" where
  "mstar_background_theorem_truth theorem_of_background true_in \<longleftrightarrow>
    (\<forall>A. theorem_of_background A \<longrightarrow> true_in Mstar_model A)"

theorem Mstar_proposition29_bullet1_from_NDS_soundness:
  assumes sound:
    "nds_background_soundness is_NDS_model theorem_of_background true_in"
    and model: "mstar_nds_model_obligation is_NDS_model"
  shows "mstar_background_theorem_truth theorem_of_background true_in"
  using sound model
  by (auto simp: nds_background_soundness_def
      mstar_nds_model_obligation_def mstar_background_theorem_truth_def)

definition mstar_proposition29_all_bullets ::
  "('formula \<Rightarrow> bool) \<Rightarrow> (mstar_model \<Rightarrow> 'formula \<Rightarrow> bool) \<Rightarrow> bool" where
  "mstar_proposition29_all_bullets theorem_of_background true_in \<longleftrightarrow>
    mstar_background_theorem_truth theorem_of_background true_in \<and>
    name_at Pstar At \<and>
    \<not> (\<exists>x \<in> De At. capp Pstar At (haec At x)) \<and>
    (\<exists>N. rigid_class_at N At \<and>
      (\<forall>Q. mstar_Name Q \<longleftrightarrow> N At Q) \<and>
      boxed_name_coverage_at N At)"

theorem Mstar_proposition29_from_NDS_soundness:
  assumes sound:
    "nds_background_soundness is_NDS_model theorem_of_background true_in"
    and model: "mstar_nds_model_obligation is_NDS_model"
  shows "mstar_proposition29_all_bullets theorem_of_background true_in"
proof -
  have bullet1:
    "mstar_background_theorem_truth theorem_of_background true_in"
    using sound model by (rule Mstar_proposition29_bullet1_from_NDS_soundness)
  show ?thesis
    using bullet1 Pstar_is_Name bullet3_P_is_empty Mstar_name_plenitude_witness
    by (auto simp: mstar_proposition29_all_bullets_def)
qed

theorem Mstar_proposition29_core:
  "name_at Pstar At \<and>
   \<not> (\<exists>x \<in> De At. capp Pstar At (haec At x)) \<and>
   (\<forall>w x. x \<in> De w \<longrightarrow>
      (\<exists>Q. (Q = Astar \<or> Q = Pstar) \<and> name_at Q w \<and> capp Q w (haec w x))) \<and>
   (\<exists>N. rigid_class_at N At \<and>
      (\<forall>Q. mstar_Name Q \<longleftrightarrow> N At Q) \<and>
      boxed_name_coverage_at N At)"
  using Pstar_is_Name bullet3_P_is_empty Mstar_name_coverage
    Mstar_name_plenitude_witness by blast

theorem Mstar_proposition29_finite_bullets:
  "name_at Pstar At \<and>
   \<not> (\<exists>x \<in> De At. capp Pstar At (haec At x)) \<and>
   (\<exists>N. rigid_class_at N At \<and>
      (\<forall>Q. mstar_Name Q \<longleftrightarrow> N At Q) \<and>
      boxed_name_coverage_at N At)"
  using Pstar_is_Name bullet3_P_is_empty Mstar_name_plenitude_witness by blast

end
