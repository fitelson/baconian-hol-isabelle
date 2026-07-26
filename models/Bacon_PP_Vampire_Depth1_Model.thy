theory Bacon_PP_Vampire_Depth1_Model
  imports Main
begin

section \<open>Isabelle certificate for the bounded Vampire model\<close>

text \<open>
  This theory checks the concrete three-proposition, three-operator
  interpretation printed by Vampire for
  \<open>goodman_pp_recombination_depth1.in\<close>.  It certifies only that bounded
  first-order benchmark, not the full PP schema stock or Goodman's consistency
  conjecture.
\<close>

datatype vprop = VP1 | VP2 | VP3
datatype vop = VO1 | VO2 | VO3

fun vapp :: "vop \<Rightarrow> vprop \<Rightarrow> vprop" where
  "vapp VO1 VP1 = VP1"
| "vapp VO1 VP2 = VP3"
| "vapp VO1 VP3 = VP3"
| "vapp VO2 P = P"
| "vapp VO3 VP1 = VP2"
| "vapp VO3 VP2 = VP3"
| "vapp VO3 VP3 = VP2"

fun vneg :: "vprop \<Rightarrow> vprop" where
  "vneg VP1 = VP2"
| "vneg VP2 = VP3"
| "vneg VP3 = VP2"

fun vholds :: "vprop \<Rightarrow> bool" where
  "vholds VP1 = True"
| "vholds VP2 = False"
| "vholds VP3 = True"

fun vpure :: "vop \<Rightarrow> bool" where
  "vpure VO1 = True"
| "vpure VO2 = True"
| "vpure VO3 = True"

fun vfundamental :: "vprop \<Rightarrow> bool" where
  "vfundamental VP1 = False"
| "vfundamental VP2 = True"
| "vfundamental VP3 = False"

fun vfun_prime :: "vprop \<Rightarrow> bool" where
  "vfun_prime VP1 = False"
| "vfun_prime VP2 = False"
| "vfun_prime VP3 = False"

abbreviation vtop :: vprop where "vtop \<equiv> VP1"
abbreviation vbottom :: vprop where "vbottom \<equiv> VP2"
abbreviation vd :: vop where "vd \<equiv> VO1"
abbreviation videntity :: vop where "videntity \<equiv> VO2"
abbreviation vnegation :: vop where "vnegation \<equiv> VO3"

lemma v_top_true:
  "vholds vtop"
  by simp

lemma v_bottom_false:
  "\<not> vholds vbottom"
  by simp

lemma v_neg_truth:
  "vholds (vneg P) \<longleftrightarrow> \<not> vholds P"
  by (cases P) simp_all

lemma v_identity_beta:
  "vapp videntity P = P"
  by simp

lemma v_negation_beta:
  "vapp vnegation P = vneg P"
  by (cases P) simp_all

lemma v_identity_pure:
  "vpure videntity"
  by simp

lemma v_negation_pure:
  "vpure vnegation"
  by simp

lemma v_liar_pure:
  "vpure vd"
  by simp

lemma v_application_collision:
  "\<exists>X Y. vpure X \<and> vpure Y \<and>
      vapp X P = vapp Y P \<and> X \<noteq> Y"
proof (cases P)
  case VP1
  then show ?thesis
    by (intro exI[of _ VO1] exI[of _ VO2]) simp
next
  case VP2
  then show ?thesis
    by (intro exI[of _ VO1] exI[of _ VO3]) simp
next
  case VP3
  then show ?thesis
    by (intro exI[of _ VO1] exI[of _ VO2]) simp
qed

lemma v_fun_prime_definition:
  "vfun_prime P \<longleftrightarrow>
    (\<forall>X Y. (vpure X \<and> vpure Y \<and> vapp X P = vapp Y P)
      \<longrightarrow> X = Y)"
proof
  assume "vfun_prime P"
  then show "\<forall>X Y. (vpure X \<and> vpure Y \<and> vapp X P = vapp Y P)
      \<longrightarrow> X = Y"
    by (cases P) simp_all
next
  assume separating:
    "\<forall>X Y. (vpure X \<and> vpure Y \<and> vapp X P = vapp Y P)
      \<longrightarrow> X = Y"
  obtain X Y where
      "vpure X" "vpure Y" "vapp X P = vapp Y P" "X \<noteq> Y"
    using v_application_collision[of P] by blast
  with separating show "vfun_prime P"
    by blast
qed

lemma v_fun_prime_false:
  "\<not> vfun_prime P"
  by (cases P) simp_all

lemma v_liar_matrix:
  "vholds (vapp vd P) \<longleftrightarrow>
    (\<forall>X Q. (vpure X \<and> vfun_prime Q \<and> P = vapp X Q)
      \<longrightarrow> \<not> vholds (vapp X P))"
  by (cases P; simp add: v_fun_prime_false)

lemma v_fundamental_iff:
  "vfundamental P \<longleftrightarrow> P = VP2"
  by (cases P) simp_all

lemma v_unique_fundamental:
  "\<exists>R. vfundamental R \<and>
    (\<forall>Q. vfundamental Q \<longrightarrow> Q = R)"
  by (rule exI[of _ VP2]) (simp add: v_fundamental_iff)

lemma v_unary_recombination:
  "\<forall>X R. (vpure X \<and> vfundamental R \<and> vapp X R = vtop)
    \<longrightarrow> (\<forall>Q. vholds (vapp X Q))"
proof (intro allI)
  fix X R
  show "(vpure X \<and> vfundamental R \<and> vapp X R = vtop)
      \<longrightarrow> (\<forall>Q. vholds (vapp X Q))"
    by (cases X; cases R; simp)
qed

definition v_depth1_axioms_hold :: bool where
  "v_depth1_axioms_hold \<longleftrightarrow>
      vholds vtop
    \<and> \<not> vholds vbottom
    \<and> (\<forall>P. vholds (vneg P) \<longleftrightarrow> \<not> vholds P)
    \<and> (\<forall>P. vapp videntity P = P)
    \<and> (\<forall>P. vapp vnegation P = vneg P)
    \<and> vpure videntity
    \<and> vpure vnegation
    \<and> vpure vd
    \<and> (\<forall>P. vfun_prime P \<longleftrightarrow>
          (\<forall>X Y. (vpure X \<and> vpure Y \<and> vapp X P = vapp Y P)
            \<longrightarrow> X = Y))
    \<and> (\<forall>P. vholds (vapp vd P) \<longleftrightarrow>
          (\<forall>X Q. (vpure X \<and> vfun_prime Q \<and> P = vapp X Q)
            \<longrightarrow> \<not> vholds (vapp X P)))
    \<and> (\<exists>R. vfundamental R \<and>
          (\<forall>Q. vfundamental Q \<longrightarrow> Q = R))
    \<and> (\<forall>X R. (vpure X \<and> vfundamental R \<and> vapp X R = vtop)
          \<longrightarrow> (\<forall>Q. vholds (vapp X Q)))"

theorem v_depth1_model_certificate:
  v_depth1_axioms_hold
  unfolding v_depth1_axioms_hold_def
  by (simp add: v_neg_truth v_identity_beta v_negation_beta
      v_fun_prime_definition v_liar_matrix v_unique_fundamental
      v_unary_recombination; metis v_unary_recombination)

end
