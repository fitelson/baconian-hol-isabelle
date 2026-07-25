theory Bacon_PP_Action_Model
  imports Bacon_PP
begin

section \<open>Bacon substitution actions\<close>

text \<open>
  Bacon's substitution models begin with a monoid of substitutions and an
  action of that monoid on every semantic domain.  We isolate the algebraic
  laws first, independently of the later choice of certified pure elements.
\<close>

locale bacon_monoid =
  fixes bunit :: "'m"
    and bcomp :: "'m \<Rightarrow> 'm \<Rightarrow> 'm"
  assumes bcomp_left_unit[simp]: "bcomp bunit i = i"
    and bcomp_right_unit[simp]: "bcomp i bunit = i"
    and bcomp_assoc: "bcomp (bcomp i j) k = bcomp i (bcomp j k)"

locale bacon_action = bacon_monoid bunit bcomp
  for bunit :: "'m"
    and bcomp :: "'m \<Rightarrow> 'm \<Rightarrow> 'm" +
  fixes bact :: "'m \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes bact_unit[simp]: "bact bunit a = a"
    and bact_comp: "bact i (bact j a) = bact (bcomp i j) a"
begin

definition action_invariant :: "'a \<Rightarrow> bool" where
  "action_invariant a \<longleftrightarrow> (\<forall>i. bact i a = a)"

lemma action_invariantI:
  assumes "\<And>i. bact i a = a"
  shows "action_invariant a"
  using assms unfolding action_invariant_def by blast

lemma action_invariantD:
  assumes "action_invariant a"
  shows "bact i a = a"
  using assms unfolding action_invariant_def by blast

end

subsection \<open>The finite-word monoid and division action\<close>

type_synonym bacon_word = "nat list"
type_synonym bacon_proposition = "bacon_word set"
type_synonym bacon_prop_operator =
  "bacon_proposition \<Rightarrow> bacon_proposition"

interpretation bacon_words: bacon_monoid "[]" "(@)"
  by unfold_locales (simp_all add: append_assoc)

definition bacon_word_divide ::
    "bacon_word \<Rightarrow> bacon_proposition \<Rightarrow> bacon_proposition" where
  "bacon_word_divide i P = {j. j @ i \<in> P}"

interpretation bacon_word_action:
  bacon_action "[]" "(@)" bacon_word_divide
proof
  fix P :: bacon_proposition
  show "bacon_word_divide [] P = P"
    by (auto simp: bacon_word_divide_def)
next
  fix i j :: bacon_word
    and P :: bacon_proposition
  show "bacon_word_divide i (bacon_word_divide j P) =
      bacon_word_divide (i @ j) P"
    by (auto simp: bacon_word_divide_def append_assoc)
qed

definition bacon_word_true :: "bacon_proposition \<Rightarrow> bool" where
  "bacon_word_true P \<longleftrightarrow> [] \<in> P"

lemma bacon_word_true_after_divide_iff:
  "bacon_word_true (bacon_word_divide i P) \<longleftrightarrow> i \<in> P"
  by (simp add: bacon_word_true_def bacon_word_divide_def)

definition bacon_word_box ::
    "bacon_proposition \<Rightarrow> bacon_proposition" where
  "bacon_word_box P = {i. \<forall>j. j @ i \<in> P}"

lemma bacon_word_box_truth_iff:
  "bacon_word_true (bacon_word_box P) \<longleftrightarrow> P = UNIV"
  by (auto simp: bacon_word_true_def bacon_word_box_def)

definition bacon_word_lift ::
    "bacon_word \<Rightarrow> bacon_proposition \<Rightarrow> bacon_proposition" where
  "bacon_word_lift i P = {j @ i | j. j \<in> P}"

lemma bacon_word_divide_lift[simp]:
  "bacon_word_divide i (bacon_word_lift i P) = P"
  by (auto simp: bacon_word_divide_def bacon_word_lift_def)

theorem bacon_word_divide_surjective:
  "surj (bacon_word_divide i)"
unfolding surj_def
proof
  fix P :: bacon_proposition
  show "\<exists>Q. P = bacon_word_divide i Q"
    using bacon_word_divide_lift[of i P] by blast
qed

subsection \<open>An explicit proposition with a faithful substitution orbit\<close>

text \<open>
  The proposition below records every word behind a one-symbol marker encoding
  that very word.  Its right quotients are all distinct.  This supplies a
  concrete algebraic analogue of the generic fundamental proposition required
  in Bacon's gluing argument.
\<close>

definition bacon_generic_r :: bacon_proposition where
  "bacon_generic_r =
    {ys. \<exists>xs. ys = [list_encode xs] @ xs}"

lemma bacon_generic_r_marker_iff[simp]:
  "[n] @ xs \<in> bacon_generic_r \<longleftrightarrow> n = list_encode xs"
  by (auto simp: bacon_generic_r_def list_encode_eq)

lemma bacon_generic_r_own_marker[simp]:
  "[list_encode i] \<in> bacon_word_divide i bacon_generic_r"
  unfolding bacon_word_divide_def bacon_generic_r_def
  by (intro CollectI exI[of _ i]) simp

lemma bacon_generic_r_fresh_marker:
  "[Suc (list_encode i)] \<notin> bacon_word_divide i bacon_generic_r"
  using bacon_generic_r_marker_iff[of "Suc (list_encode i)" i]
  by (simp add: bacon_word_divide_def)

lemma bacon_generic_r_quotient_not_UNIV:
  "bacon_word_divide i bacon_generic_r \<noteq> UNIV"
  using bacon_generic_r_fresh_marker[of i] by blast

theorem bacon_generic_r_orbit_injective:
  "inj (\<lambda>i. bacon_word_divide i bacon_generic_r)"
proof (rule injI)
  fix i j
  assume quotients:
    "bacon_word_divide i bacon_generic_r =
      bacon_word_divide j bacon_generic_r"
  have "[list_encode i] \<in> bacon_word_divide j bacon_generic_r"
    using bacon_generic_r_own_marker[of i] quotients by simp
  then have "list_encode i = list_encode j"
    using bacon_generic_r_marker_iff[of "list_encode i" j]
    by (simp add: bacon_word_divide_def)
  then show "i = j"
    by (simp add: list_encode_eq)
qed

section \<open>Invariant operators and the QSS obstruction\<close>

definition bacon_equivariant_operator ::
    "bacon_prop_operator \<Rightarrow> bool" where
  "bacon_equivariant_operator F \<longleftrightarrow>
    (\<forall>i P.
      bacon_word_divide i (F P) =
      F (bacon_word_divide i P))"

definition bacon_invariant_operator ::
    "bacon_proposition set \<Rightarrow> bacon_prop_operator" where
  "bacon_invariant_operator T P =
    {i. bacon_word_divide i P \<in> T}"

lemma bacon_invariant_operator_equivariant:
  "bacon_equivariant_operator (bacon_invariant_operator T)"
  unfolding bacon_equivariant_operator_def
proof (intro allI)
  fix i :: bacon_word
    and P :: bacon_proposition
  show "bacon_word_divide i (bacon_invariant_operator T P) =
      bacon_invariant_operator T (bacon_word_divide i P)"
    by (auto simp: bacon_word_divide_def bacon_invariant_operator_def
        append_assoc)
qed

lemma bacon_invariant_operator_injective:
  "inj bacon_invariant_operator"
proof (rule injI)
  fix T U :: "bacon_proposition set"
  assume operators:
    "bacon_invariant_operator T = bacon_invariant_operator U"
  show "T = U"
  proof (rule set_eqI)
    fix P :: bacon_proposition
    have operator_values:
        "bacon_invariant_operator T P =
          bacon_invariant_operator U P"
      using operators by (rule fun_cong)
    have
        "([] \<in> bacon_invariant_operator T P) =
          ([] \<in> bacon_invariant_operator U P)"
      using operator_values by simp
    then show "P \<in> T \<longleftrightarrow> P \<in> U"
      by (simp add: bacon_invariant_operator_def bacon_word_divide_def)
  qed
qed

definition bacon_false_operator :: bacon_prop_operator where
  "bacon_false_operator = (\<lambda>_. {})"

definition bacon_universal_test_operator :: bacon_prop_operator where
  "bacon_universal_test_operator =
    bacon_invariant_operator {UNIV}"

lemma bacon_false_operator_equivariant:
  "bacon_equivariant_operator bacon_false_operator"
  by (simp add: bacon_equivariant_operator_def bacon_false_operator_def
      bacon_word_divide_def)

lemma bacon_universal_test_operator_equivariant:
  "bacon_equivariant_operator bacon_universal_test_operator"
  unfolding bacon_universal_test_operator_def
  by (rule bacon_invariant_operator_equivariant)

lemma bacon_universal_test_operator_generic_r[simp]:
  "bacon_universal_test_operator bacon_generic_r = {}"
proof (rule set_eqI)
  fix i
  show "i \<in> bacon_universal_test_operator bacon_generic_r \<longleftrightarrow>
      i \<in> {}"
    using bacon_generic_r_quotient_not_UNIV[of i]
    by (simp add: bacon_universal_test_operator_def
        bacon_invariant_operator_def)
qed

lemma bacon_universal_test_operator_UNIV[simp]:
  "bacon_universal_test_operator UNIV = UNIV"
  by (auto simp: bacon_universal_test_operator_def
      bacon_invariant_operator_def bacon_word_divide_def)

lemma bacon_false_operator_generic_r[simp]:
  "bacon_false_operator bacon_generic_r = {}"
  by (simp add: bacon_false_operator_def)

lemma bacon_false_operator_UNIV[simp]:
  "bacon_false_operator UNIV = {}"
  by (simp add: bacon_false_operator_def)

lemma bacon_universal_test_operator_distinct:
  "bacon_universal_test_operator \<noteq> bacon_false_operator"
proof
  assume equal: "bacon_universal_test_operator = bacon_false_operator"
  have
      "bacon_universal_test_operator UNIV =
        bacon_false_operator UNIV"
    using equal by (rule fun_cong)
  then show False
    by simp
qed

theorem bacon_full_invariance_QSS_collision:
  "\<exists>F G.
    bacon_equivariant_operator F \<and>
    bacon_equivariant_operator G \<and>
    F \<noteq> G \<and>
    F bacon_generic_r = G bacon_generic_r"
  using bacon_universal_test_operator_equivariant
    bacon_false_operator_equivariant
    bacon_universal_test_operator_distinct
  by (intro exI[of _ bacon_universal_test_operator]
      exI[of _ bacon_false_operator]) simp

subsection \<open>A concrete certified-purity seed\<close>

text \<open>
  Full invariance is too large, but the obstruction does not show that every
  restricted purity interpretation fails.  The following seed interprets pure
  propositions as the two substitution-invariant extremes.  Its own purity
  predicate is an equivariant unary operator.  Certifying that operator is the
  lower-type instance \<open>Pure(Pure_Prop)\<close>, not the conjectured target
  \<open>Pure(Pure_(Prop-to-Prop))\<close>, which lives one type higher.  The lower-type
  seed satisfies zero-ary QLN, closure under applying its purity predicate,
  unary QLN at the generic proposition, and QSS within its singleton certified
  unary fragment.  It is a typed diagnostic, not yet a model of target PP.
\<close>

definition bacon_certified_proposition ::
    "bacon_proposition \<Rightarrow> bool" where
  "bacon_certified_proposition P \<longleftrightarrow> P = {} \<or> P = UNIV"

definition bacon_pure_predicate :: bacon_prop_operator where
  "bacon_pure_predicate =
    bacon_invariant_operator {{}, UNIV}"

definition bacon_seed_certified_unary ::
    "bacon_prop_operator \<Rightarrow> bool" where
  "bacon_seed_certified_unary F \<longleftrightarrow> F = bacon_pure_predicate"

definition bacon_zeroary_QLN_condition ::
    "bacon_proposition \<Rightarrow> bool" where
  "bacon_zeroary_QLN_condition P \<longleftrightarrow>
    (P = UNIV) = bacon_word_true P"

definition bacon_unary_QLN_condition ::
    "bacon_proposition \<Rightarrow> bacon_prop_operator \<Rightarrow> bool" where
  "bacon_unary_QLN_condition R F \<longleftrightarrow>
    (F R = UNIV) = (\<forall>P. bacon_word_true (F P))"

definition bacon_QSS_condition ::
    "(bacon_prop_operator \<Rightarrow> bool) \<Rightarrow>
      bacon_proposition \<Rightarrow> bool" where
  "bacon_QSS_condition certified R \<longleftrightarrow>
    (\<forall>F G. certified F \<longrightarrow> certified G \<longrightarrow>
      F R = G R \<longrightarrow> F = G)"

theorem bacon_full_invariance_not_QSS:
  "\<not> bacon_QSS_condition
    bacon_equivariant_operator bacon_generic_r"
  using bacon_full_invariance_QSS_collision
  unfolding bacon_QSS_condition_def
  by blast

lemma bacon_generic_r_quotient_nonempty:
  "bacon_word_divide i bacon_generic_r \<noteq> {}"
  using bacon_generic_r_own_marker[of i] by blast

lemma bacon_pure_predicate_equivariant:
  "bacon_equivariant_operator bacon_pure_predicate"
  unfolding bacon_pure_predicate_def
  by (rule bacon_invariant_operator_equivariant)

lemma bacon_pure_predicate_on_empty[simp]:
  "bacon_pure_predicate {} = UNIV"
  by (auto simp: bacon_pure_predicate_def bacon_invariant_operator_def
      bacon_word_divide_def)

lemma bacon_pure_predicate_on_UNIV[simp]:
  "bacon_pure_predicate UNIV = UNIV"
  by (auto simp: bacon_pure_predicate_def bacon_invariant_operator_def
      bacon_word_divide_def)

lemma bacon_pure_predicate_generic_r[simp]:
  "bacon_pure_predicate bacon_generic_r = {}"
proof (rule set_eqI)
  fix i
  have nonempty:
      "bacon_word_divide i bacon_generic_r \<noteq> {}"
    by (rule bacon_generic_r_quotient_nonempty)
  have nonuniversal:
      "bacon_word_divide i bacon_generic_r \<noteq> UNIV"
    by (rule bacon_generic_r_quotient_not_UNIV)
  show "i \<in> bacon_pure_predicate bacon_generic_r \<longleftrightarrow> i \<in> {}"
    using nonempty nonuniversal
    by (simp add: bacon_pure_predicate_def bacon_invariant_operator_def)
qed

lemma bacon_certified_proposition_zeroary_QLN:
  assumes "bacon_certified_proposition P"
  shows "bacon_zeroary_QLN_condition P"
  using assms
  by (auto simp: bacon_certified_proposition_def
      bacon_zeroary_QLN_condition_def bacon_word_true_def)

lemma bacon_pure_predicate_certified:
  "bacon_seed_certified_unary bacon_pure_predicate"
  by (simp add: bacon_seed_certified_unary_def)

lemma bacon_pure_predicate_application_closed:
  assumes "bacon_certified_proposition P"
  shows "bacon_certified_proposition (bacon_pure_predicate P)"
  using assms
  by (auto simp: bacon_certified_proposition_def)

lemma bacon_empty_word_singleton_not_certified:
  "\<not> bacon_certified_proposition {[]}"
proof -
  have "{[]} \<noteq> (UNIV :: bacon_proposition)"
  proof
    assume singleton_universal:
      "{[]} = (UNIV :: bacon_proposition)"
    have universal_subset:
        "(UNIV :: bacon_proposition) \<subseteq> {[]}"
      using singleton_universal by blast
    have "[0] \<in> (UNIV :: bacon_proposition)"
      by simp
    have "[0] \<in> {[]}"
      using universal_subset \<open>[0] \<in> (UNIV :: bacon_proposition)\<close>
      by blast
    then show False
      by simp
  qed
  then show ?thesis
    by (simp add: bacon_certified_proposition_def)
qed

lemma bacon_pure_predicate_not_universally_true:
  "\<not> (\<forall>P. bacon_word_true (bacon_pure_predicate P))"
proof
  assume all_true:
    "\<forall>P. bacon_word_true (bacon_pure_predicate P)"
  have "bacon_word_true (bacon_pure_predicate {[]})"
    using all_true by blast
  then have "{[]} \<in> {{}, (UNIV :: bacon_proposition)}"
    by (simp add: bacon_word_true_def bacon_pure_predicate_def
        bacon_invariant_operator_def bacon_word_divide_def)
  then show False
    using bacon_empty_word_singleton_not_certified
    by (auto simp: bacon_certified_proposition_def)
qed

lemma bacon_pure_predicate_unary_QLN:
  "bacon_unary_QLN_condition bacon_generic_r bacon_pure_predicate"
  using bacon_pure_predicate_not_universally_true
  by (simp add: bacon_unary_QLN_condition_def)

lemma bacon_seed_certified_unary_QSS:
  "bacon_QSS_condition bacon_seed_certified_unary bacon_generic_r"
  by (auto simp: bacon_QSS_condition_def bacon_seed_certified_unary_def)

theorem bacon_certified_purity_seed:
  "bacon_equivariant_operator bacon_pure_predicate \<and>
    bacon_seed_certified_unary bacon_pure_predicate \<and>
    (\<forall>P. bacon_certified_proposition P \<longrightarrow>
      bacon_zeroary_QLN_condition P) \<and>
    (\<forall>P. bacon_certified_proposition P \<longrightarrow>
      bacon_certified_proposition (bacon_pure_predicate P)) \<and>
    bacon_unary_QLN_condition bacon_generic_r bacon_pure_predicate \<and>
    bacon_QSS_condition bacon_seed_certified_unary bacon_generic_r"
  using bacon_pure_predicate_equivariant
    bacon_pure_predicate_certified
    bacon_certified_proposition_zeroary_QLN
    bacon_pure_predicate_application_closed
    bacon_pure_predicate_unary_QLN
    bacon_seed_certified_unary_QSS
  by blast

subsection \<open>Closing the seed under basic logical unary operations\<close>

text \<open>
  Ordinary logical Purity already requires more than the singleton unary seed.
  At type proposition-to-proposition it includes identity, negation, and the
  constant truth and falsity operators.  These four denotations preserve
  equivariance, application closure, world-indexed unary QLN, and QSS at the
  generic proposition.  Adjoining \<open>Pure_Prop\<close> and certifying it would instead
  impose a lower-type PP instance not present in the target theory; that
  stronger core fails QSS because the purity predicate and constant falsity
  agree at the generic proposition.
\<close>

definition bacon_identity_operator :: bacon_prop_operator where
  "bacon_identity_operator P = P"

definition bacon_complement_operator :: bacon_prop_operator where
  "bacon_complement_operator P = - P"

definition bacon_true_operator :: bacon_prop_operator where
  "bacon_true_operator P = UNIV"

definition bacon_logical_unary_core ::
    "bacon_prop_operator \<Rightarrow> bool" where
  "bacon_logical_unary_core F \<longleftrightarrow>
    F = bacon_identity_operator \<or>
    F = bacon_complement_operator \<or>
    F = bacon_true_operator \<or>
    F = bacon_false_operator"

definition bacon_lower_PP_unary_core ::
    "bacon_prop_operator \<Rightarrow> bool" where
  "bacon_lower_PP_unary_core F \<longleftrightarrow>
    bacon_logical_unary_core F \<or> F = bacon_pure_predicate"

lemma bacon_identity_operator_equivariant:
  "bacon_equivariant_operator bacon_identity_operator"
  by (simp add: bacon_equivariant_operator_def bacon_identity_operator_def)

lemma bacon_complement_operator_equivariant:
  "bacon_equivariant_operator bacon_complement_operator"
  by (auto simp: bacon_equivariant_operator_def
      bacon_complement_operator_def bacon_word_divide_def)

lemma bacon_true_operator_equivariant:
  "bacon_equivariant_operator bacon_true_operator"
  by (auto simp: bacon_equivariant_operator_def bacon_true_operator_def
      bacon_word_divide_def)

lemma bacon_logical_unary_core_equivariant:
  assumes "bacon_logical_unary_core F"
  shows "bacon_equivariant_operator F"
  using assms bacon_identity_operator_equivariant
    bacon_complement_operator_equivariant
    bacon_true_operator_equivariant
    bacon_false_operator_equivariant
  unfolding bacon_logical_unary_core_def
  by blast

lemma bacon_logical_unary_core_application_closed:
  assumes "bacon_logical_unary_core F"
    and "bacon_certified_proposition P"
  shows "bacon_certified_proposition (F P)"
  using assms
  by (auto simp: bacon_logical_unary_core_def
      bacon_certified_proposition_def bacon_identity_operator_def
      bacon_complement_operator_def bacon_true_operator_def
      bacon_false_operator_def)

lemma bacon_generic_r_nonempty:
  "bacon_generic_r \<noteq> {}"
proof -
  have "[list_encode []] \<in>
      bacon_word_divide [] bacon_generic_r"
    by (rule bacon_generic_r_own_marker)
  then have "[list_encode []] \<in> bacon_generic_r"
    by (simp add: bacon_word_divide_def)
  then show ?thesis
    by blast
qed

lemma bacon_generic_r_not_UNIV:
  "bacon_generic_r \<noteq> UNIV"
  using bacon_generic_r_quotient_not_UNIV[of "[]"]
  by (simp add: bacon_word_divide_def)

definition bacon_unary_QLN_at_world ::
    "bacon_word \<Rightarrow> bacon_proposition \<Rightarrow>
      bacon_prop_operator \<Rightarrow> bool" where
  "bacon_unary_QLN_at_world i R F \<longleftrightarrow>
    (bacon_word_divide i (F R) = UNIV) = (\<forall>P. i \<in> F P)"

definition bacon_unary_QLN_valid ::
    "bacon_proposition \<Rightarrow> bacon_prop_operator \<Rightarrow> bool" where
  "bacon_unary_QLN_valid R F \<longleftrightarrow>
    (\<forall>i. bacon_unary_QLN_at_world i R F)"

lemma bacon_unary_QLN_valid_imp_actual:
  assumes "bacon_unary_QLN_valid R F"
  shows "bacon_unary_QLN_condition R F"
proof -
  have "bacon_unary_QLN_at_world [] R F"
    using assms unfolding bacon_unary_QLN_valid_def by blast
  then show ?thesis
    by (simp add: bacon_unary_QLN_at_world_def
        bacon_unary_QLN_condition_def bacon_word_divide_def
        bacon_word_true_def)
qed

lemma bacon_identity_operator_unary_QLN_valid:
  "bacon_unary_QLN_valid bacon_generic_r bacon_identity_operator"
proof (unfold bacon_unary_QLN_valid_def
    bacon_unary_QLN_at_world_def, intro allI)
  fix i
  have left_false:
      "bacon_word_divide i
        (bacon_identity_operator bacon_generic_r) \<noteq> UNIV"
    using bacon_generic_r_quotient_not_UNIV[of i]
    by (simp add: bacon_identity_operator_def)
  have right_false:
      "\<not> (\<forall>P. i \<in> bacon_identity_operator P)"
    by (auto simp: bacon_identity_operator_def)
  show "(bacon_word_divide i
      (bacon_identity_operator bacon_generic_r) = UNIV) =
      (\<forall>P. i \<in> bacon_identity_operator P)"
    using left_false right_false by blast
qed

lemma bacon_complement_operator_unary_QLN_valid:
  "bacon_unary_QLN_valid bacon_generic_r bacon_complement_operator"
proof (unfold bacon_unary_QLN_valid_def
    bacon_unary_QLN_at_world_def, intro allI)
  fix i
  have left_false:
      "bacon_word_divide i
        (bacon_complement_operator bacon_generic_r) \<noteq> UNIV"
    using bacon_generic_r_quotient_nonempty[of i]
    by (auto simp: bacon_complement_operator_def bacon_word_divide_def)
  have right_false:
      "\<not> (\<forall>P. i \<in> bacon_complement_operator P)"
    by (auto simp: bacon_complement_operator_def)
  show "(bacon_word_divide i
      (bacon_complement_operator bacon_generic_r) = UNIV) =
      (\<forall>P. i \<in> bacon_complement_operator P)"
    using left_false right_false by blast
qed

lemma bacon_true_operator_unary_QLN_valid:
  "bacon_unary_QLN_valid bacon_generic_r bacon_true_operator"
  by (auto simp: bacon_unary_QLN_valid_def
      bacon_unary_QLN_at_world_def bacon_true_operator_def
      bacon_word_divide_def)

lemma bacon_false_operator_unary_QLN_valid:
  "bacon_unary_QLN_valid bacon_generic_r bacon_false_operator"
  by (auto simp: bacon_unary_QLN_valid_def
      bacon_unary_QLN_at_world_def bacon_false_operator_def
      bacon_word_divide_def)

lemma bacon_pure_predicate_unary_QLN_valid:
  "bacon_unary_QLN_valid bacon_generic_r bacon_pure_predicate"
proof (unfold bacon_unary_QLN_valid_def
    bacon_unary_QLN_at_world_def, intro allI)
  fix i
  have left_false:
      "bacon_word_divide i
        (bacon_pure_predicate bacon_generic_r) \<noteq> UNIV"
    by (simp add: bacon_word_divide_def)
  have not_true:
      "i \<notin> bacon_pure_predicate
        (bacon_word_lift i {[]})"
    using bacon_empty_word_singleton_not_certified
    by (simp add: bacon_pure_predicate_def
        bacon_invariant_operator_def bacon_certified_proposition_def)
  have right_false:
      "\<not> (\<forall>P. i \<in> bacon_pure_predicate P)"
    using not_true by blast
  show "(bacon_word_divide i
      (bacon_pure_predicate bacon_generic_r) = UNIV) =
      (\<forall>P. i \<in> bacon_pure_predicate P)"
    using left_false right_false by blast
qed

theorem bacon_logical_unary_core_QLN_valid:
  assumes "bacon_logical_unary_core F"
  shows "bacon_unary_QLN_valid bacon_generic_r F"
  using assms bacon_identity_operator_unary_QLN_valid
    bacon_complement_operator_unary_QLN_valid
    bacon_true_operator_unary_QLN_valid
    bacon_false_operator_unary_QLN_valid
  unfolding bacon_logical_unary_core_def
  by blast

lemma bacon_identity_operator_unary_QLN:
  "bacon_unary_QLN_condition bacon_generic_r bacon_identity_operator"
  using bacon_identity_operator_unary_QLN_valid
  by (rule bacon_unary_QLN_valid_imp_actual)

lemma bacon_complement_operator_unary_QLN:
  "bacon_unary_QLN_condition bacon_generic_r bacon_complement_operator"
  using bacon_complement_operator_unary_QLN_valid
  by (rule bacon_unary_QLN_valid_imp_actual)

lemma bacon_true_operator_unary_QLN:
  "bacon_unary_QLN_condition bacon_generic_r bacon_true_operator"
  using bacon_true_operator_unary_QLN_valid
  by (rule bacon_unary_QLN_valid_imp_actual)

lemma bacon_false_operator_unary_QLN:
  "bacon_unary_QLN_condition bacon_generic_r bacon_false_operator"
  using bacon_false_operator_unary_QLN_valid
  by (rule bacon_unary_QLN_valid_imp_actual)

theorem bacon_logical_unary_core_QLN:
  assumes "bacon_logical_unary_core F"
  shows "bacon_unary_QLN_condition bacon_generic_r F"
  using assms bacon_identity_operator_unary_QLN
    bacon_complement_operator_unary_QLN
    bacon_true_operator_unary_QLN
    bacon_false_operator_unary_QLN
  unfolding bacon_logical_unary_core_def
  by blast

lemma bacon_pure_predicate_distinct_false_operator:
  "bacon_pure_predicate \<noteq> bacon_false_operator"
proof
  assume operators_equal:
    "bacon_pure_predicate = bacon_false_operator"
  have "bacon_pure_predicate UNIV = bacon_false_operator UNIV"
    using operators_equal by (rule fun_cong)
  then show False
    by simp
qed

lemma bacon_generic_r_not_own_complement:
  "bacon_generic_r \<noteq> - bacon_generic_r"
proof
  assume equal:
    "bacon_generic_r = - bacon_generic_r"
  have "([] \<in> bacon_generic_r) = ([] \<in> - bacon_generic_r)"
    using equal by simp
  then show False
    by simp
qed

theorem bacon_logical_unary_core_QSS:
  "bacon_QSS_condition bacon_logical_unary_core bacon_generic_r"
proof (unfold bacon_QSS_condition_def, intro allI impI)
  fix F G
  assume F_core: "bacon_logical_unary_core F"
    and G_core: "bacon_logical_unary_core G"
    and agreement: "F bacon_generic_r = G bacon_generic_r"
  show "F = G"
    using F_core G_core agreement
      bacon_generic_r_nonempty bacon_generic_r_not_UNIV
      bacon_generic_r_not_own_complement
    by (auto simp: bacon_logical_unary_core_def
        bacon_identity_operator_def bacon_complement_operator_def
        bacon_true_operator_def bacon_false_operator_def)
qed

theorem bacon_lower_PP_unary_core_not_QSS:
  "\<not> bacon_QSS_condition bacon_lower_PP_unary_core bacon_generic_r"
proof
  assume qss:
    "bacon_QSS_condition bacon_lower_PP_unary_core bacon_generic_r"
  have pure_in_core:
      "bacon_lower_PP_unary_core bacon_pure_predicate"
    by (simp add: bacon_lower_PP_unary_core_def)
  have false_in_core:
      "bacon_lower_PP_unary_core bacon_false_operator"
    by (simp add: bacon_lower_PP_unary_core_def
        bacon_logical_unary_core_def)
  have agreement:
      "bacon_pure_predicate bacon_generic_r =
        bacon_false_operator bacon_generic_r"
    by (simp add: bacon_false_operator_def)
  have "bacon_pure_predicate = bacon_false_operator"
    using qss pure_in_core false_in_core agreement
    unfolding bacon_QSS_condition_def
    by blast
  then show False
    using bacon_pure_predicate_distinct_false_operator by contradiction
qed

theorem bacon_logical_unary_core_package:
  "(\<forall>F. bacon_logical_unary_core F \<longrightarrow>
      bacon_equivariant_operator F) \<and>
    (\<forall>F P. bacon_logical_unary_core F \<longrightarrow>
      bacon_certified_proposition P \<longrightarrow>
      bacon_certified_proposition (F P)) \<and>
    (\<forall>F. bacon_logical_unary_core F \<longrightarrow>
      bacon_unary_QLN_valid bacon_generic_r F) \<and>
    (\<forall>F. bacon_logical_unary_core F \<longrightarrow>
      bacon_unary_QLN_condition bacon_generic_r F) \<and>
    bacon_QSS_condition bacon_logical_unary_core bacon_generic_r"
  using bacon_logical_unary_core_equivariant
    bacon_logical_unary_core_application_closed
    bacon_logical_unary_core_QLN_valid
    bacon_logical_unary_core_QLN
    bacon_logical_unary_core_QSS
  by blast

theorem bacon_lower_PP_unary_core_package:
  "(\<forall>F. bacon_lower_PP_unary_core F \<longrightarrow>
      bacon_equivariant_operator F) \<and>
    (\<forall>F P. bacon_lower_PP_unary_core F \<longrightarrow>
      bacon_certified_proposition P \<longrightarrow>
      bacon_certified_proposition (F P)) \<and>
    (\<forall>F. bacon_lower_PP_unary_core F \<longrightarrow>
      bacon_unary_QLN_valid bacon_generic_r F) \<and>
    \<not> bacon_QSS_condition bacon_lower_PP_unary_core bacon_generic_r"
  using bacon_logical_unary_core_equivariant
    bacon_pure_predicate_equivariant
    bacon_logical_unary_core_application_closed
    bacon_pure_predicate_application_closed
    bacon_logical_unary_core_QLN_valid
    bacon_pure_predicate_unary_QLN_valid
    bacon_lower_PP_unary_core_not_QSS
  unfolding bacon_lower_PP_unary_core_def
  by blast

subsection \<open>The correctly typed target-PP seed\<close>

text \<open>
  The conjectured PP instance is one level above \<open>Pure_Prop\<close>.
  Its inner denotation \<open>Pure_(Prop-to-Prop)\<close> is a classifier of unary
  propositional operators.  The next predicate classifies entities of that
  classifier type.  The following two-level seed represents exactly this type
  pattern.  It verifies target PP and the two adjacent application-closure
  instances, but it does not yet close the classifier level under every closed
  logical term.
\<close>

type_synonym bacon_unary_classifier =
  "bacon_prop_operator \<Rightarrow> bacon_proposition"

definition bacon_pure_unary_classifier :: bacon_unary_classifier where
  "bacon_pure_unary_classifier F =
    (if bacon_logical_unary_core F then UNIV else {})"

definition bacon_certified_unary_classifier ::
    "bacon_unary_classifier \<Rightarrow> bool" where
  "bacon_certified_unary_classifier K \<longleftrightarrow>
    K = bacon_pure_unary_classifier"

definition bacon_target_PP_seed :: bool where
  "bacon_target_PP_seed \<longleftrightarrow>
    bacon_certified_unary_classifier bacon_pure_unary_classifier"

lemma bacon_pure_unary_classifier_on_core[simp]:
  assumes "bacon_logical_unary_core F"
  shows "bacon_pure_unary_classifier F = UNIV"
  using assms by (simp add: bacon_pure_unary_classifier_def)

lemma bacon_pure_unary_classifier_off_core[simp]:
  assumes "\<not> bacon_logical_unary_core F"
  shows "bacon_pure_unary_classifier F = {}"
  using assms by (simp add: bacon_pure_unary_classifier_def)

lemma bacon_target_PP_seed_holds:
  "bacon_target_PP_seed"
  by (simp add: bacon_target_PP_seed_def
      bacon_certified_unary_classifier_def)

lemma bacon_target_PP_seed_application_closed:
  assumes "bacon_certified_unary_classifier K"
    and "bacon_logical_unary_core F"
  shows "bacon_certified_proposition (K F)"
  using assms
  by (simp add: bacon_certified_unary_classifier_def
      bacon_certified_proposition_def)

lemma bacon_pure_unary_classifier_output_invariant:
  assumes "bacon_logical_unary_core F"
  shows "bacon_word_divide i (bacon_pure_unary_classifier F) =
    bacon_pure_unary_classifier F"
  using assms by (simp add: bacon_word_divide_def)

theorem bacon_typed_target_PP_seed_package:
  "bacon_target_PP_seed \<and>
    (\<forall>F P. bacon_logical_unary_core F \<longrightarrow>
      bacon_certified_proposition P \<longrightarrow>
      bacon_certified_proposition (F P)) \<and>
    (\<forall>K F. bacon_certified_unary_classifier K \<longrightarrow>
      bacon_logical_unary_core F \<longrightarrow>
      bacon_certified_proposition (K F)) \<and>
    (\<forall>i F. bacon_logical_unary_core F \<longrightarrow>
      bacon_word_divide i (bacon_pure_unary_classifier F) =
        bacon_pure_unary_classifier F)"
  using bacon_target_PP_seed_holds
    bacon_logical_unary_core_application_closed
    bacon_target_PP_seed_application_closed
    bacon_pure_unary_classifier_output_invariant
  by blast

subsection \<open>First classifier-level logical closure\<close>

definition bacon_true_unary_classifier :: bacon_unary_classifier where
  "bacon_true_unary_classifier F = UNIV"

definition bacon_false_unary_classifier :: bacon_unary_classifier where
  "bacon_false_unary_classifier F = {}"

definition bacon_forall_unary_classifier :: bacon_unary_classifier where
  "bacon_forall_unary_classifier F = {i. \<forall>P. i \<in> F P}"

definition bacon_exists_unary_classifier :: bacon_unary_classifier where
  "bacon_exists_unary_classifier F = {i. \<exists>P. i \<in> F P}"

definition bacon_identity_test_classifier :: bacon_unary_classifier where
  "bacon_identity_test_classifier F =
    (if F = bacon_identity_operator then UNIV else {})"

definition bacon_classifier_logical_core ::
    "bacon_unary_classifier \<Rightarrow> bool" where
  "bacon_classifier_logical_core K \<longleftrightarrow>
    K = bacon_true_unary_classifier \<or>
    K = bacon_false_unary_classifier \<or>
    K = bacon_forall_unary_classifier \<or>
    K = bacon_exists_unary_classifier \<or>
    K = bacon_identity_test_classifier"

definition bacon_target_classifier_core ::
    "bacon_unary_classifier \<Rightarrow> bool" where
  "bacon_target_classifier_core K \<longleftrightarrow>
    bacon_classifier_logical_core K \<or>
    K = bacon_pure_unary_classifier"

lemma bacon_certified_proposition_invariant:
  assumes "bacon_certified_proposition P"
  shows "bacon_word_divide i P = P"
  using assms
  by (auto simp: bacon_certified_proposition_def bacon_word_divide_def)

lemma bacon_forall_classifier_on_identity[simp]:
  "bacon_forall_unary_classifier bacon_identity_operator = {}"
  by (auto simp: bacon_forall_unary_classifier_def
      bacon_identity_operator_def)

lemma bacon_forall_classifier_on_complement[simp]:
  "bacon_forall_unary_classifier bacon_complement_operator = {}"
  by (auto simp: bacon_forall_unary_classifier_def
      bacon_complement_operator_def)

lemma bacon_forall_classifier_on_true[simp]:
  "bacon_forall_unary_classifier bacon_true_operator = UNIV"
  by (auto simp: bacon_forall_unary_classifier_def
      bacon_true_operator_def)

lemma bacon_forall_classifier_on_false[simp]:
  "bacon_forall_unary_classifier bacon_false_operator = {}"
  by (auto simp: bacon_forall_unary_classifier_def
      bacon_false_operator_def)

lemma bacon_exists_classifier_on_identity[simp]:
  "bacon_exists_unary_classifier bacon_identity_operator = UNIV"
  by (auto simp: bacon_exists_unary_classifier_def
      bacon_identity_operator_def)

lemma bacon_exists_classifier_on_complement[simp]:
  "bacon_exists_unary_classifier bacon_complement_operator = UNIV"
  by (auto simp: bacon_exists_unary_classifier_def
      bacon_complement_operator_def)

lemma bacon_exists_classifier_on_true[simp]:
  "bacon_exists_unary_classifier bacon_true_operator = UNIV"
  by (auto simp: bacon_exists_unary_classifier_def
      bacon_true_operator_def)

lemma bacon_exists_classifier_on_false[simp]:
  "bacon_exists_unary_classifier bacon_false_operator = {}"
  by (auto simp: bacon_exists_unary_classifier_def
      bacon_false_operator_def)

lemma bacon_complement_operator_distinct_identity:
  "bacon_complement_operator \<noteq> bacon_identity_operator"
proof
  assume equal:
    "bacon_complement_operator = bacon_identity_operator"
  have "bacon_complement_operator bacon_generic_r =
      bacon_identity_operator bacon_generic_r"
    using equal by (rule fun_cong)
  then show False
    using bacon_generic_r_not_own_complement
    by (simp add: bacon_complement_operator_def bacon_identity_operator_def)
qed

lemma bacon_true_operator_distinct_identity:
  "bacon_true_operator \<noteq> bacon_identity_operator"
proof
  assume equal:
    "bacon_true_operator = bacon_identity_operator"
  have "bacon_true_operator bacon_generic_r =
      bacon_identity_operator bacon_generic_r"
    using equal by (rule fun_cong)
  then show False
    using bacon_generic_r_not_UNIV
    by (simp add: bacon_true_operator_def bacon_identity_operator_def)
qed

lemma bacon_false_operator_distinct_identity:
  "bacon_false_operator \<noteq> bacon_identity_operator"
proof
  assume equal:
    "bacon_false_operator = bacon_identity_operator"
  have "bacon_false_operator bacon_generic_r =
      bacon_identity_operator bacon_generic_r"
    using equal by (rule fun_cong)
  then show False
    using bacon_generic_r_nonempty
    by (simp add: bacon_false_operator_def bacon_identity_operator_def)
qed

lemma bacon_classifier_logical_core_application_closed:
  assumes "bacon_classifier_logical_core K"
    and "bacon_logical_unary_core F"
  shows "bacon_certified_proposition (K F)"
  using assms
    bacon_complement_operator_distinct_identity
    bacon_true_operator_distinct_identity
    bacon_false_operator_distinct_identity
  by (auto simp: bacon_classifier_logical_core_def
      bacon_logical_unary_core_def bacon_certified_proposition_def
      bacon_true_unary_classifier_def bacon_false_unary_classifier_def
      bacon_identity_test_classifier_def)

lemma bacon_target_classifier_core_contains_PP:
  "bacon_target_classifier_core bacon_pure_unary_classifier"
  by (simp add: bacon_target_classifier_core_def)

lemma bacon_target_classifier_core_application_closed:
  assumes "bacon_target_classifier_core K"
    and "bacon_logical_unary_core F"
  shows "bacon_certified_proposition (K F)"
  using assms bacon_classifier_logical_core_application_closed
  by (auto simp: bacon_target_classifier_core_def
      bacon_pure_unary_classifier_def bacon_certified_proposition_def)

lemma bacon_target_classifier_core_output_invariant:
  assumes "bacon_target_classifier_core K"
    and "bacon_logical_unary_core F"
  shows "bacon_word_divide i (K F) = K F"
  using bacon_target_classifier_core_application_closed[OF assms]
  by (rule bacon_certified_proposition_invariant)

theorem bacon_classifier_level_closure_package:
  "bacon_target_classifier_core bacon_pure_unary_classifier \<and>
    (\<forall>K F. bacon_target_classifier_core K \<longrightarrow>
      bacon_logical_unary_core F \<longrightarrow>
      bacon_certified_proposition (K F)) \<and>
    (\<forall>i K F. bacon_target_classifier_core K \<longrightarrow>
      bacon_logical_unary_core F \<longrightarrow>
      bacon_word_divide i (K F) = K F)"
  using bacon_target_classifier_core_contains_PP
    bacon_target_classifier_core_application_closed
    bacon_target_classifier_core_output_invariant
  by blast

subsection \<open>Boolean closure of the target classifier level\<close>

definition bacon_characteristic_unary_classifier ::
    "bacon_prop_operator set \<Rightarrow> bacon_unary_classifier" where
  "bacon_characteristic_unary_classifier S F =
    (if F \<in> S then UNIV else {})"

definition bacon_boolean_unary_classifier ::
    "bacon_unary_classifier \<Rightarrow> bool" where
  "bacon_boolean_unary_classifier K \<longleftrightarrow>
    (\<exists>S. K = bacon_characteristic_unary_classifier S)"

definition bacon_classifier_complement ::
    "bacon_unary_classifier \<Rightarrow> bacon_unary_classifier" where
  "bacon_classifier_complement K F = - K F"

definition bacon_classifier_conjunction ::
    "bacon_unary_classifier \<Rightarrow> bacon_unary_classifier \<Rightarrow>
      bacon_unary_classifier" where
  "bacon_classifier_conjunction K L F = K F \<inter> L F"

definition bacon_classifier_disjunction ::
    "bacon_unary_classifier \<Rightarrow> bacon_unary_classifier \<Rightarrow>
      bacon_unary_classifier" where
  "bacon_classifier_disjunction K L F = K F \<union> L F"

lemma bacon_pure_unary_classifier_characteristic:
  "bacon_pure_unary_classifier =
    bacon_characteristic_unary_classifier
      {F. bacon_logical_unary_core F}"
  by (rule ext)
    (simp add: bacon_pure_unary_classifier_def
      bacon_characteristic_unary_classifier_def)

lemma bacon_boolean_unary_classifier_contains_PP:
  "bacon_boolean_unary_classifier bacon_pure_unary_classifier"
  unfolding bacon_boolean_unary_classifier_def
  using bacon_pure_unary_classifier_characteristic by blast

lemma bacon_boolean_unary_classifier_application_closed:
  assumes "bacon_boolean_unary_classifier K"
  shows "bacon_certified_proposition (K F)"
proof -
  obtain S where
      "K = bacon_characteristic_unary_classifier S"
    using assms unfolding bacon_boolean_unary_classifier_def by blast
  then show ?thesis
    by (simp add: bacon_characteristic_unary_classifier_def
        bacon_certified_proposition_def)
qed

lemma bacon_boolean_unary_classifier_output_invariant:
  assumes "bacon_boolean_unary_classifier K"
  shows "bacon_word_divide i (K F) = K F"
  using bacon_boolean_unary_classifier_application_closed[OF assms]
  by (rule bacon_certified_proposition_invariant)

lemma bacon_boolean_unary_classifier_complement_closed:
  assumes "bacon_boolean_unary_classifier K"
  shows "bacon_boolean_unary_classifier (bacon_classifier_complement K)"
proof -
  obtain S where K:
      "K = bacon_characteristic_unary_classifier S"
    using assms unfolding bacon_boolean_unary_classifier_def by blast
  have "bacon_classifier_complement K =
      bacon_characteristic_unary_classifier (- S)"
    by (rule ext)
      (auto simp: K bacon_classifier_complement_def
        bacon_characteristic_unary_classifier_def)
  then show ?thesis
    unfolding bacon_boolean_unary_classifier_def by blast
qed

lemma bacon_boolean_unary_classifier_conjunction_closed:
  assumes "bacon_boolean_unary_classifier K"
    and "bacon_boolean_unary_classifier L"
  shows "bacon_boolean_unary_classifier
    (bacon_classifier_conjunction K L)"
proof -
  obtain S T where K:
      "K = bacon_characteristic_unary_classifier S"
    and L:
      "L = bacon_characteristic_unary_classifier T"
    using assms unfolding bacon_boolean_unary_classifier_def by blast
  have "bacon_classifier_conjunction K L =
      bacon_characteristic_unary_classifier (S \<inter> T)"
    by (rule ext)
      (auto simp: K L bacon_classifier_conjunction_def
        bacon_characteristic_unary_classifier_def)
  then show ?thesis
    unfolding bacon_boolean_unary_classifier_def by blast
qed

lemma bacon_boolean_unary_classifier_disjunction_closed:
  assumes "bacon_boolean_unary_classifier K"
    and "bacon_boolean_unary_classifier L"
  shows "bacon_boolean_unary_classifier
    (bacon_classifier_disjunction K L)"
proof -
  obtain S T where K:
      "K = bacon_characteristic_unary_classifier S"
    and L:
      "L = bacon_characteristic_unary_classifier T"
    using assms unfolding bacon_boolean_unary_classifier_def by blast
  have "bacon_classifier_disjunction K L =
      bacon_characteristic_unary_classifier (S \<union> T)"
    by (rule ext)
      (auto simp: K L bacon_classifier_disjunction_def
        bacon_characteristic_unary_classifier_def)
  then show ?thesis
    unfolding bacon_boolean_unary_classifier_def by blast
qed

theorem bacon_boolean_target_PP_package:
  "bacon_boolean_unary_classifier bacon_pure_unary_classifier \<and>
    (\<forall>K F. bacon_boolean_unary_classifier K \<longrightarrow>
      bacon_certified_proposition (K F)) \<and>
    (\<forall>i K F. bacon_boolean_unary_classifier K \<longrightarrow>
      bacon_word_divide i (K F) = K F) \<and>
    (\<forall>K. bacon_boolean_unary_classifier K \<longrightarrow>
      bacon_boolean_unary_classifier (bacon_classifier_complement K)) \<and>
    (\<forall>K L. bacon_boolean_unary_classifier K \<longrightarrow>
      bacon_boolean_unary_classifier L \<longrightarrow>
      bacon_boolean_unary_classifier
        (bacon_classifier_conjunction K L)) \<and>
    (\<forall>K L. bacon_boolean_unary_classifier K \<longrightarrow>
      bacon_boolean_unary_classifier L \<longrightarrow>
      bacon_boolean_unary_classifier
        (bacon_classifier_disjunction K L))"
  using bacon_boolean_unary_classifier_contains_PP
    bacon_boolean_unary_classifier_application_closed
    bacon_boolean_unary_classifier_output_invariant
    bacon_boolean_unary_classifier_complement_closed
    bacon_boolean_unary_classifier_conjunction_closed
    bacon_boolean_unary_classifier_disjunction_closed
  by blast

subsection \<open>The forced PP diagonal and the present model obstruction\<close>

text \<open>
  In the intended world-relative reading, applying
  \<open>Pure_(Prop-to-Prop)\<close> to the constant operator \<open>K P\<close> asks whether
  the current view of \<open>P\<close> is one of the certified extreme propositions.
  Thus the already defined \<open>bacon_pure_predicate\<close> gives precisely the
  resulting proposition on constant operators.  PP plus logical/application
  closure then forces the diagonal operator
  \<open>F(P) = not Pure(K P)\<close> to be certified.  For the present generic
  proposition every view is nonextreme, so \<open>F(r)\<close> is universal.  This makes
  the Recombination half of unary QLN fail.  The theorem below therefore
  identifies the first exact failure of this concrete seed; it is not an
  inconsistency proof for the abstract PP theory.
\<close>

definition bacon_constant_operator ::
    "bacon_proposition \<Rightarrow> bacon_prop_operator" where
  "bacon_constant_operator P Q = P"

lemma bacon_pure_predicate_world_relative_constant_iff:
  "i \<in> bacon_pure_predicate P \<longleftrightarrow>
    bacon_certified_proposition (bacon_word_divide i P)"
  by (simp add: bacon_pure_predicate_def
      bacon_invariant_operator_def bacon_certified_proposition_def)

definition bacon_PP_diagonal_operator :: bacon_prop_operator where
  "bacon_PP_diagonal_operator P = - bacon_pure_predicate P"

lemma bacon_PP_diagonal_operator_equivariant:
  "bacon_equivariant_operator bacon_PP_diagonal_operator"
proof (unfold bacon_equivariant_operator_def, intro allI)
  fix i P
  have pure_equivariance:
      "bacon_word_divide i (bacon_pure_predicate P) =
        bacon_pure_predicate (bacon_word_divide i P)"
    using bacon_pure_predicate_equivariant
    unfolding bacon_equivariant_operator_def by blast
  show "bacon_word_divide i (bacon_PP_diagonal_operator P) =
      bacon_PP_diagonal_operator (bacon_word_divide i P)"
    using pure_equivariance
    by (auto simp: bacon_PP_diagonal_operator_def bacon_word_divide_def)
qed

lemma bacon_PP_diagonal_on_generic_r[simp]:
  "bacon_PP_diagonal_operator bacon_generic_r = UNIV"
  by (simp add: bacon_PP_diagonal_operator_def)

lemma bacon_PP_diagonal_on_empty[simp]:
  "bacon_PP_diagonal_operator {} = {}"
  by (simp add: bacon_PP_diagonal_operator_def)

theorem bacon_PP_diagonal_not_unary_QLN:
  "\<not> bacon_unary_QLN_condition
    bacon_generic_r bacon_PP_diagonal_operator"
proof -
  have empty_not_true:
      "\<not> bacon_word_true (bacon_PP_diagonal_operator {})"
    by (simp add: bacon_word_true_def)
  have not_universally_true:
      "\<not> (\<forall>P. bacon_word_true (bacon_PP_diagonal_operator P))"
    using empty_not_true by blast
  show ?thesis
    using not_universally_true
    by (simp add: bacon_unary_QLN_condition_def)
qed

corollary bacon_PP_diagonal_not_unary_QLN_valid:
  "\<not> bacon_unary_QLN_valid
    bacon_generic_r bacon_PP_diagonal_operator"
  using bacon_PP_diagonal_not_unary_QLN
    bacon_unary_QLN_valid_imp_actual
  by blast

theorem bacon_current_seed_cannot_certify_forced_diagonal:
  assumes certified_implies_QLN:
    "\<And>F. certified F \<Longrightarrow>
      bacon_unary_QLN_valid bacon_generic_r F"
  shows "\<not> certified bacon_PP_diagonal_operator"
  using certified_implies_QLN
    bacon_PP_diagonal_not_unary_QLN_valid
  by blast

definition bacon_diagonal_from_classifier ::
    "bacon_prop_operator \<Rightarrow> bacon_prop_operator" where
  "bacon_diagonal_from_classifier C P = - C P"

theorem bacon_QLN_forces_diagonal_transition:
  assumes qln:
      "bacon_unary_QLN_condition R
        (bacon_diagonal_from_classifier C)"
    and certified_witness:
      "bacon_word_true (C P)"
    and diagonal_true:
      "bacon_word_true (bacon_diagonal_from_classifier C R)"
  shows "[] \<notin> C R \<and> C R \<noteq> {}"
proof
  show "[] \<notin> C R"
    using diagonal_true
    by (simp add: bacon_word_true_def
        bacon_diagonal_from_classifier_def)
next
  have witness_not_true:
      "\<not> bacon_word_true (bacon_diagonal_from_classifier C P)"
    using certified_witness
    by (simp add: bacon_word_true_def
        bacon_diagonal_from_classifier_def)
  have not_universally_true:
      "\<not> (\<forall>Q.
        bacon_word_true (bacon_diagonal_from_classifier C Q))"
    using witness_not_true by blast
  have diagonal_not_UNIV:
      "bacon_diagonal_from_classifier C R \<noteq> UNIV"
    using qln not_universally_true
    unfolding bacon_unary_QLN_condition_def
    by blast
  show "C R \<noteq> {}"
  proof
    assume "C R = {}"
    then have "bacon_diagonal_from_classifier C R = UNIV"
      by (simp add: bacon_diagonal_from_classifier_def)
    then show False
      using diagonal_not_UNIV by contradiction
  qed
qed

corollary bacon_QLN_forces_nonactual_transition_world:
  assumes qln:
      "bacon_unary_QLN_condition R
        (bacon_diagonal_from_classifier C)"
    and certified_witness:
      "bacon_word_true (C P)"
    and diagonal_true:
      "bacon_word_true (bacon_diagonal_from_classifier C R)"
  shows "\<exists>i. i \<noteq> [] \<and> i \<in> C R"
proof -
  have transition:
      "[] \<notin> C R \<and> C R \<noteq> {}"
    by (rule bacon_QLN_forces_diagonal_transition[OF assms])
  have actual_false: "[] \<notin> C R"
    using transition by blast
  have transition_exists: "C R \<noteq> {}"
    using transition by blast
  obtain i where "i \<in> C R"
    using transition_exists by blast
  moreover have "i \<noteq> []"
    using actual_false calculation by blast
  ultimately show ?thesis
    by blast
qed

theorem bacon_faithful_orbit_views_nonextreme:
  assumes orbit_injective:
      "inj (\<lambda>i. bacon_word_divide i R)"
  shows "\<not> bacon_certified_proposition (bacon_word_divide i R)"
proof
  assume extreme:
    "bacon_certified_proposition (bacon_word_divide i R)"
  have acted:
      "bacon_word_divide [0] (bacon_word_divide i R) =
        bacon_word_divide ([0] @ i) R"
    by (rule bacon_word_action.bact_comp)
  have extreme_fixed:
      "bacon_word_divide [0] (bacon_word_divide i R) =
        bacon_word_divide i R"
  proof -
    have "bacon_word_divide i R = {} \<or>
        bacon_word_divide i R = UNIV"
      using extreme
      unfolding bacon_certified_proposition_def .
    then show ?thesis
    proof
      assume quotient_empty:
        "bacon_word_divide i R = {}"
      show ?thesis
      proof -
        have "bacon_word_divide [0] (bacon_word_divide i R) =
            bacon_word_divide [0] {}"
          using quotient_empty by simp
        also have "... = {}"
          by (simp add: bacon_word_divide_def)
        also have "... = bacon_word_divide i R"
          using quotient_empty by simp
        finally show ?thesis .
      qed
    next
      assume quotient_universal:
        "bacon_word_divide i R = UNIV"
      show ?thesis
      proof -
        have "bacon_word_divide [0] (bacon_word_divide i R) =
            bacon_word_divide [0] UNIV"
          using quotient_universal by simp
        also have "... = UNIV"
          by (simp add: bacon_word_divide_def)
        also have "... = bacon_word_divide i R"
          using quotient_universal by simp
        finally show ?thesis .
      qed
    qed
  qed
  have orbit_collision:
      "bacon_word_divide ([0] @ i) R =
        bacon_word_divide i R"
    using acted extreme_fixed by simp
  have "[0] @ i = i"
    using orbit_injective orbit_collision
    by (rule injD)
  then show False
    by simp
qed

corollary bacon_generic_orbit_views_nonextreme:
  "\<not> bacon_certified_proposition
    (bacon_word_divide i bacon_generic_r)"
  using bacon_generic_r_orbit_injective
  by (rule bacon_faithful_orbit_views_nonextreme)

theorem bacon_faithful_orbit_extreme_view_classifier_empty:
  assumes orbit_injective:
      "inj (\<lambda>i. bacon_word_divide i R)"
  shows "{i. bacon_certified_proposition
      (bacon_word_divide i R)} = {}"
  using bacon_faithful_orbit_views_nonextreme[OF orbit_injective]
  by blast

text \<open>
  Consequently the transition forced by the diagonal cannot be implemented by
  declaring \<open>K P\<close> pure exactly when \<open>P\<close> is an extreme proposition.  A
  tempting repair is to certify a constant operator \<open>K (i dot r)\<close> while
  leaving its value \<open>i dot r\<close> impure.  The construction below verifies that
  this repairs the diagonal's actual-world QLN biconditional and preserves
  QSS.  It then isolates the decisive defect: application closure immediately
  transfers purity from a constant operator to its value.  Thus this tempting
  repair is a diagnostic no-go result, not yet a model fragment of the full
  theory.
\<close>

subsection \<open>The minimal transition and its application-closure obstruction\<close>

text \<open>
  We now realize that necessary transition explicitly.  Injectivity of the
  generic orbit implies that at most one word has view \<open>-r\<close>.  Hence one of
  the two nonempty words \<open>[0]\<close> and \<open>[1]\<close> has a view distinct from the
  complement of \<open>r\<close>.  We select such a word and adjoin the corresponding
  constant operator to the four-element logical unary core.
\<close>

definition bacon_transition_word :: bacon_word where
  "bacon_transition_word =
    (if bacon_word_divide [0] bacon_generic_r \<noteq> - bacon_generic_r
     then [0] else [1])"

lemma bacon_transition_word_nonempty:
  "bacon_transition_word \<noteq> []"
  by (simp add: bacon_transition_word_def)

lemma bacon_transition_view_not_complement:
  "bacon_word_divide bacon_transition_word bacon_generic_r
    \<noteq> - bacon_generic_r"
proof (cases
    "bacon_word_divide [0] bacon_generic_r \<noteq> - bacon_generic_r")
  case True
  then show ?thesis
    by (simp add: bacon_transition_word_def)
next
  case False
  then have zero_view:
      "bacon_word_divide [0] bacon_generic_r = - bacon_generic_r"
    by simp
  have selected_word:
      "bacon_transition_word = [1]"
    by (simp add: bacon_transition_word_def False)
  show ?thesis
  proof
    assume selected_view:
      "bacon_word_divide bacon_transition_word bacon_generic_r =
        - bacon_generic_r"
    have one_view:
        "bacon_word_divide [1] bacon_generic_r = - bacon_generic_r"
      using selected_view selected_word by simp
    have quotient_collision:
        "bacon_word_divide [0] bacon_generic_r =
          bacon_word_divide [1] bacon_generic_r"
      using zero_view one_view by simp
    have word_collision: "([0] :: bacon_word) = [1]"
      using quotient_collision
      by (rule injD[OF bacon_generic_r_orbit_injective])
    show "False"
      using word_collision by simp
  qed
qed

definition bacon_transition_view :: bacon_proposition where
  "bacon_transition_view =
    bacon_word_divide bacon_transition_word bacon_generic_r"

lemma bacon_transition_view_not_generic:
  "bacon_transition_view \<noteq> bacon_generic_r"
proof
  assume views_equal:
      "bacon_transition_view = bacon_generic_r"
  have quotient_collision:
      "bacon_word_divide bacon_transition_word bacon_generic_r =
        bacon_word_divide [] bacon_generic_r"
    using views_equal
    by (simp add: bacon_transition_view_def)
  have "bacon_transition_word = []"
    using bacon_generic_r_orbit_injective quotient_collision
    by (rule injD)
  then show False
    using bacon_transition_word_nonempty by contradiction
qed

lemma bacon_transition_view_not_complement_generic:
  "bacon_transition_view \<noteq> - bacon_generic_r"
  using bacon_transition_view_not_complement
  by (simp add: bacon_transition_view_def)

lemma bacon_transition_view_nonempty:
  "bacon_transition_view \<noteq> {}"
  using bacon_generic_r_quotient_nonempty[of bacon_transition_word]
  by (simp add: bacon_transition_view_def)

lemma bacon_transition_view_not_UNIV:
  "bacon_transition_view \<noteq> UNIV"
  using bacon_generic_r_quotient_not_UNIV[of bacon_transition_word]
  by (simp add: bacon_transition_view_def)

theorem bacon_transition_view_not_pure:
  "\<not> bacon_certified_proposition bacon_transition_view"
  using bacon_generic_orbit_views_nonextreme[of bacon_transition_word]
  by (simp add: bacon_transition_view_def)

lemma bacon_constant_operator_injective:
  "inj bacon_constant_operator"
proof (rule injI)
  fix P Q
  assume constants_equal:
      "bacon_constant_operator P = bacon_constant_operator Q"
  have "bacon_constant_operator P {} = bacon_constant_operator Q {}"
    using constants_equal by (rule fun_cong)
  then show "P = Q"
    by (simp add: bacon_constant_operator_def)
qed

definition bacon_transition_certified_unary ::
    "bacon_prop_operator \<Rightarrow> bool" where
  "bacon_transition_certified_unary F \<longleftrightarrow>
    bacon_logical_unary_core F \<or>
    F = bacon_constant_operator bacon_transition_view"

lemma bacon_transition_constant_certified:
  "bacon_transition_certified_unary
    (bacon_constant_operator bacon_transition_view)"
  by (simp add: bacon_transition_certified_unary_def)

lemma bacon_logical_unary_core_value_at_generic:
  assumes "bacon_logical_unary_core F"
  shows "F bacon_generic_r = bacon_generic_r \<or>
    F bacon_generic_r = - bacon_generic_r \<or>
    F bacon_generic_r = UNIV \<or>
    F bacon_generic_r = {}"
  using assms
  by (auto simp: bacon_logical_unary_core_def
      bacon_identity_operator_def bacon_complement_operator_def
      bacon_true_operator_def bacon_false_operator_def)

lemma bacon_transition_constant_not_logical_core:
  "\<not> bacon_logical_unary_core
    (bacon_constant_operator bacon_transition_view)"
proof
  assume core:
      "bacon_logical_unary_core
        (bacon_constant_operator bacon_transition_view)"
  have value_cases:
      "bacon_transition_view = bacon_generic_r \<or>
        bacon_transition_view = - bacon_generic_r \<or>
        bacon_transition_view = UNIV \<or>
        bacon_transition_view = {}"
    using bacon_logical_unary_core_value_at_generic[OF core]
    by (simp add: bacon_constant_operator_def)
  show False
    using value_cases
      bacon_transition_view_not_generic
      bacon_transition_view_not_complement_generic
      bacon_transition_view_nonempty
      bacon_transition_view_not_UNIV
    by blast
qed

theorem bacon_transition_certified_unary_QSS:
  "bacon_QSS_condition
    bacon_transition_certified_unary bacon_generic_r"
proof (unfold bacon_QSS_condition_def, intro allI impI)
  fix F G
  assume F_certified: "bacon_transition_certified_unary F"
    and G_certified: "bacon_transition_certified_unary G"
    and agreement: "F bacon_generic_r = G bacon_generic_r"
  show "F = G"
  proof (cases "bacon_logical_unary_core F")
    case F_core: True
    show ?thesis
    proof (cases "bacon_logical_unary_core G")
      case G_core: True
      show ?thesis
        using bacon_logical_unary_core_QSS F_core G_core agreement
        unfolding bacon_QSS_condition_def by blast
    next
      case G_not_core: False
      then have G_transition:
          "G = bacon_constant_operator bacon_transition_view"
        using G_certified
        unfolding bacon_transition_certified_unary_def by blast
      have value_cases:
          "F bacon_generic_r = bacon_generic_r \<or>
            F bacon_generic_r = - bacon_generic_r \<or>
            F bacon_generic_r = UNIV \<or>
            F bacon_generic_r = {}"
        by (rule bacon_logical_unary_core_value_at_generic[OF F_core])
      have contradiction_fact: False
        using agreement G_transition value_cases
          bacon_transition_view_not_generic
          bacon_transition_view_not_complement_generic
          bacon_transition_view_nonempty
          bacon_transition_view_not_UNIV
        by (simp add: bacon_constant_operator_def)
      then show ?thesis
        by blast
    qed
  next
    case F_not_core: False
    then have F_transition:
        "F = bacon_constant_operator bacon_transition_view"
      using F_certified
      unfolding bacon_transition_certified_unary_def by blast
    show ?thesis
    proof (cases "bacon_logical_unary_core G")
      case G_core: True
      have value_cases:
          "G bacon_generic_r = bacon_generic_r \<or>
            G bacon_generic_r = - bacon_generic_r \<or>
            G bacon_generic_r = UNIV \<or>
            G bacon_generic_r = {}"
        by (rule bacon_logical_unary_core_value_at_generic[OF G_core])
      have contradiction_fact: False
        using agreement F_transition value_cases
          bacon_transition_view_not_generic
          bacon_transition_view_not_complement_generic
          bacon_transition_view_nonempty
          bacon_transition_view_not_UNIV
        by (simp add: bacon_constant_operator_def)
      then show ?thesis
        by blast
    next
      case G_not_core: False
      then have G_transition:
          "G = bacon_constant_operator bacon_transition_view"
        using G_certified
        unfolding bacon_transition_certified_unary_def by blast
      show ?thesis
        using F_transition G_transition by simp
    qed
  qed
qed

definition bacon_constant_view_certification :: bacon_prop_operator where
  "bacon_constant_view_certification P =
    {i. bacon_transition_certified_unary
      (bacon_constant_operator (bacon_word_divide i P))}"

lemma bacon_constant_view_certification_as_invariant:
  "bacon_constant_view_certification =
    bacon_invariant_operator
      {P. bacon_transition_certified_unary
        (bacon_constant_operator P)}"
  by (rule ext)
    (simp add: bacon_constant_view_certification_def
      bacon_invariant_operator_def)

lemma bacon_constant_view_certification_equivariant:
  "bacon_equivariant_operator bacon_constant_view_certification"
  unfolding bacon_constant_view_certification_as_invariant
  by (rule bacon_invariant_operator_equivariant)

lemma bacon_transition_world_certifies_constant_view:
  "bacon_transition_word \<in>
    bacon_constant_view_certification bacon_generic_r"
proof (simp only: bacon_constant_view_certification_def mem_Collect_eq)
  show "bacon_transition_certified_unary
      (bacon_constant_operator
        (bacon_word_divide bacon_transition_word bacon_generic_r))"
    using bacon_transition_constant_certified
    by (simp only: bacon_transition_view_def)
qed

lemma bacon_generic_constant_not_logical_core:
  "\<not> bacon_logical_unary_core
    (bacon_constant_operator bacon_generic_r)"
proof
  assume core:
      "bacon_logical_unary_core
        (bacon_constant_operator bacon_generic_r)"
  then have operator_cases:
      "bacon_constant_operator bacon_generic_r =
          bacon_identity_operator \<or>
        bacon_constant_operator bacon_generic_r =
          bacon_complement_operator \<or>
        bacon_constant_operator bacon_generic_r =
          bacon_true_operator \<or>
        bacon_constant_operator bacon_generic_r =
          bacon_false_operator"
    unfolding bacon_logical_unary_core_def .
  then show False
  proof (elim disjE)
    assume equal:
        "bacon_constant_operator bacon_generic_r =
          bacon_identity_operator"
    have "bacon_generic_r = {}"
      using fun_cong[OF equal, of "{}"]
      by (simp add: bacon_constant_operator_def bacon_identity_operator_def)
    then show False
      using bacon_generic_r_nonempty by contradiction
  next
    assume equal:
        "bacon_constant_operator bacon_generic_r =
          bacon_complement_operator"
    have "bacon_generic_r = UNIV"
      using fun_cong[OF equal, of "{}"]
      by (simp add: bacon_constant_operator_def
          bacon_complement_operator_def)
    then show False
      using bacon_generic_r_not_UNIV by contradiction
  next
    assume equal:
        "bacon_constant_operator bacon_generic_r =
          bacon_true_operator"
    have "bacon_generic_r = UNIV"
      using fun_cong[OF equal, of "{}"]
      by (simp add: bacon_constant_operator_def bacon_true_operator_def)
    then show False
      using bacon_generic_r_not_UNIV by contradiction
  next
    assume equal:
        "bacon_constant_operator bacon_generic_r =
          bacon_false_operator"
    have "bacon_generic_r = {}"
      using fun_cong[OF equal, of "{}"]
      by (simp add: bacon_constant_operator_def bacon_false_operator_def)
    then show False
      using bacon_generic_r_nonempty by contradiction
  qed
qed

lemma bacon_actual_world_does_not_certify_generic_constant:
  "[] \<notin> bacon_constant_view_certification bacon_generic_r"
proof
  assume actual_certification:
      "[] \<in> bacon_constant_view_certification bacon_generic_r"
  have certified:
      "bacon_transition_certified_unary
        (bacon_constant_operator bacon_generic_r)"
    using actual_certification
    by (simp add: bacon_constant_view_certification_def
        bacon_word_divide_def)
  then have core_or_transition:
      "bacon_logical_unary_core
          (bacon_constant_operator bacon_generic_r) \<or>
        bacon_constant_operator bacon_generic_r =
          bacon_constant_operator bacon_transition_view"
    unfolding bacon_transition_certified_unary_def .
  then show False
  proof
    assume "bacon_logical_unary_core
        (bacon_constant_operator bacon_generic_r)"
    then show False
      using bacon_generic_constant_not_logical_core by contradiction
  next
    assume constants_equal:
        "bacon_constant_operator bacon_generic_r =
          bacon_constant_operator bacon_transition_view"
    have "bacon_generic_r = bacon_transition_view"
      using bacon_constant_operator_injective constants_equal
      by (rule injD)
    then show False
      using bacon_transition_view_not_generic by simp
  qed
qed

lemma bacon_empty_constant_is_certified_at_actual_world:
  "bacon_word_true (bacon_constant_view_certification {})"
  by (simp add: bacon_word_true_def
      bacon_constant_view_certification_def bacon_word_divide_def
      bacon_transition_certified_unary_def bacon_logical_unary_core_def
      bacon_constant_operator_def bacon_false_operator_def fun_eq_iff)

theorem bacon_transition_diagonal_actual_QLN:
  "bacon_unary_QLN_condition bacon_generic_r
    (bacon_diagonal_from_classifier
      bacon_constant_view_certification)"
proof -
  have diagonal_not_UNIV:
      "bacon_diagonal_from_classifier
        bacon_constant_view_certification bacon_generic_r \<noteq> UNIV"
    using bacon_transition_world_certifies_constant_view
    by (auto simp: bacon_diagonal_from_classifier_def)
  have not_universally_true:
      "\<not> (\<forall>P. bacon_word_true
        (bacon_diagonal_from_classifier
          bacon_constant_view_certification P))"
    using bacon_empty_constant_is_certified_at_actual_world
    by (auto simp: bacon_word_true_def
        bacon_diagonal_from_classifier_def)
  show ?thesis
    using diagonal_not_UNIV not_universally_true
    unfolding bacon_unary_QLN_condition_def
    by blast
qed

theorem bacon_minimal_nonactual_constant_transition:
  "\<exists>i. i \<noteq> [] \<and>
    \<not> bacon_certified_proposition
      (bacon_word_divide i bacon_generic_r) \<and>
    bacon_transition_certified_unary
      (bacon_constant_operator
        (bacon_word_divide i bacon_generic_r)) \<and>
    [] \<notin> bacon_constant_view_certification bacon_generic_r \<and>
    i \<in> bacon_constant_view_certification bacon_generic_r \<and>
    bacon_QSS_condition
      bacon_transition_certified_unary bacon_generic_r \<and>
    bacon_unary_QLN_condition bacon_generic_r
      (bacon_diagonal_from_classifier
        bacon_constant_view_certification)"
  using bacon_transition_word_nonempty
    bacon_transition_view_not_pure
    bacon_transition_constant_certified
    bacon_actual_world_does_not_certify_generic_constant
    bacon_transition_world_certifies_constant_view
    bacon_transition_certified_unary_QSS
    bacon_transition_diagonal_actual_QLN
  by (intro exI[of _ bacon_transition_word])
    (simp add: bacon_transition_view_def)

theorem bacon_application_closure_for_constant_forces_value:
  assumes application_closed:
      "\<And>F P. certified_unary F \<Longrightarrow>
        certified_proposition P \<Longrightarrow>
        certified_proposition (F P)"
    and constant_certified:
      "certified_unary (bacon_constant_operator Q)"
    and proposition_witness:
      "certified_proposition P"
  shows "certified_proposition Q"
  using application_closed[OF constant_certified proposition_witness]
  by (simp add: bacon_constant_operator_def)

theorem bacon_zeroary_QLN_and_complement_closure_force_extreme:
  assumes proposition_certified: "certified_proposition P"
    and certified_QLN:
      "\<And>Q. certified_proposition Q \<Longrightarrow>
        bacon_zeroary_QLN_condition Q"
    and complement_closed:
      "\<And>Q. certified_proposition Q \<Longrightarrow>
        certified_proposition (- Q)"
  shows "P = {} \<or> P = UNIV"
proof (cases "bacon_word_true P")
  case True
  have "P = UNIV"
    using certified_QLN[OF proposition_certified] True
    unfolding bacon_zeroary_QLN_condition_def
    by blast
  then show ?thesis
    by blast
next
  case False
  have complement_certified:
      "certified_proposition (- P)"
    by (rule complement_closed[OF proposition_certified])
  have complement_true:
      "bacon_word_true (- P)"
    using False
    by (simp add: bacon_word_true_def)
  have "- P = UNIV"
    using certified_QLN[OF complement_certified] complement_true
    unfolding bacon_zeroary_QLN_condition_def
    by blast
  then have "P = {}"
    by auto
  then show ?thesis
    by blast
qed

theorem bacon_full_closure_forbids_impure_constant_value:
  assumes constant_certified:
      "certified_unary (bacon_constant_operator Q)"
    and proposition_witness:
      "certified_proposition P"
    and application_closed:
      "\<And>F S. certified_unary F \<Longrightarrow>
        certified_proposition S \<Longrightarrow>
        certified_proposition (F S)"
    and certified_QLN:
      "\<And>S. certified_proposition S \<Longrightarrow>
        bacon_zeroary_QLN_condition S"
    and complement_closed:
      "\<And>S. certified_proposition S \<Longrightarrow>
        certified_proposition (- S)"
  shows "Q = {} \<or> Q = UNIV"
proof -
  have constant_output_certified:
      "certified_proposition
        (bacon_constant_operator Q P)"
    by (rule application_closed[
          OF constant_certified proposition_witness])
  have value_certified:
      "certified_proposition Q"
    using constant_output_certified
    by (simp add: bacon_constant_operator_def)
  show ?thesis
    by (rule bacon_zeroary_QLN_and_complement_closure_force_extreme[
          OF value_certified certified_QLN complement_closed])
qed

theorem bacon_identity_QLN_valid_forces_no_universal_view:
  assumes identity_QLN:
      "bacon_unary_QLN_valid R bacon_identity_operator"
  shows "bacon_word_divide i R \<noteq> UNIV"
proof
  assume universal_view:
      "bacon_word_divide i R = UNIV"
  have at_world:
      "bacon_unary_QLN_at_world i R bacon_identity_operator"
    using identity_QLN
    unfolding bacon_unary_QLN_valid_def by blast
  have not_universally_true:
      "\<not> (\<forall>P. i \<in> bacon_identity_operator P)"
    by (auto simp: bacon_identity_operator_def)
  show False
    using at_world universal_view not_universally_true
    unfolding bacon_unary_QLN_at_world_def
      bacon_identity_operator_def
    by blast
qed

theorem bacon_complement_QLN_valid_forces_no_empty_view:
  assumes complement_QLN:
      "bacon_unary_QLN_valid R bacon_complement_operator"
  shows "bacon_word_divide i R \<noteq> {}"
proof
  assume empty_view:
      "bacon_word_divide i R = {}"
  have at_world:
      "bacon_unary_QLN_at_world i R bacon_complement_operator"
    using complement_QLN
    unfolding bacon_unary_QLN_valid_def by blast
  have boxed_complement:
      "bacon_word_divide i
        (bacon_complement_operator R) = UNIV"
    using empty_view
    by (auto simp: bacon_complement_operator_def bacon_word_divide_def)
  have not_universally_true:
      "\<not> (\<forall>P. i \<in> bacon_complement_operator P)"
    by (auto simp: bacon_complement_operator_def)
  show False
    using at_world boxed_complement not_universally_true
    unfolding bacon_unary_QLN_at_world_def
    by blast
qed

theorem bacon_logical_QLN_valid_forces_all_views_nonextreme:
  assumes identity_QLN:
      "bacon_unary_QLN_valid R bacon_identity_operator"
    and complement_QLN:
      "bacon_unary_QLN_valid R bacon_complement_operator"
  shows "\<not> bacon_certified_proposition (bacon_word_divide i R)"
  using bacon_identity_QLN_valid_forces_no_universal_view[
      OF identity_QLN, of i]
    bacon_complement_QLN_valid_forces_no_empty_view[
      OF complement_QLN, of i]
  unfolding bacon_certified_proposition_def
  by blast

theorem bacon_word_action_constant_transition_no_go:
  assumes identity_QLN:
      "bacon_unary_QLN_valid R bacon_identity_operator"
    and complement_QLN:
      "bacon_unary_QLN_valid R bacon_complement_operator"
    and constant_certified:
      "certified_unary
        (bacon_constant_operator (bacon_word_divide i R))"
    and proposition_witness:
      "certified_proposition P"
    and application_closed:
      "\<And>F S. certified_unary F \<Longrightarrow>
        certified_proposition S \<Longrightarrow>
        certified_proposition (F S)"
    and certified_QLN:
      "\<And>S. certified_proposition S \<Longrightarrow>
        bacon_zeroary_QLN_condition S"
    and complement_closed:
      "\<And>S. certified_proposition S \<Longrightarrow>
        certified_proposition (- S)"
  shows False
proof -
  have constant_output_certified:
      "certified_proposition
        (bacon_constant_operator (bacon_word_divide i R) P)"
    by (rule application_closed[
          OF constant_certified proposition_witness])
  have view_certified:
      "certified_proposition (bacon_word_divide i R)"
    using constant_output_certified
    by (simp add: bacon_constant_operator_def)
  have extreme_view:
      "bacon_word_divide i R = {} \<or>
        bacon_word_divide i R = UNIV"
    by (rule bacon_zeroary_QLN_and_complement_closure_force_extreme[
          where certified_proposition=certified_proposition,
          OF view_certified certified_QLN complement_closed])
  have nonextreme_view:
      "\<not> bacon_certified_proposition (bacon_word_divide i R)"
    by (rule bacon_logical_QLN_valid_forces_all_views_nonextreme[
          OF identity_QLN complement_QLN])
  show False
    using extreme_view nonextreme_view
    unfolding bacon_certified_proposition_def
    by blast
qed

theorem bacon_transition_stock_not_application_closed:
  "\<not> (\<forall>F P.
    bacon_transition_certified_unary F \<longrightarrow>
    bacon_certified_proposition P \<longrightarrow>
    bacon_certified_proposition (F P))"
proof
  assume application_closed:
      "\<forall>F P.
        bacon_transition_certified_unary F \<longrightarrow>
        bacon_certified_proposition P \<longrightarrow>
        bacon_certified_proposition (F P)"
  have empty_certified:
      "bacon_certified_proposition {}"
    by (simp add: bacon_certified_proposition_def)
  have constant_output_certified:
      "bacon_certified_proposition
        (bacon_constant_operator bacon_transition_view {})"
    using application_closed
      bacon_transition_constant_certified empty_certified
    by blast
  have transition_value_certified:
      "bacon_certified_proposition bacon_transition_view"
    using constant_output_certified
    by (simp add: bacon_constant_operator_def)
  show False
    using transition_value_certified bacon_transition_view_not_pure
    by contradiction
qed

corollary bacon_requested_impure_value_transition_is_not_a_full_model_step:
  "bacon_transition_certified_unary
      (bacon_constant_operator bacon_transition_view) \<and>
    \<not> bacon_certified_proposition bacon_transition_view \<and>
    bacon_QSS_condition
      bacon_transition_certified_unary bacon_generic_r \<and>
    bacon_unary_QLN_condition bacon_generic_r
      (bacon_diagonal_from_classifier
        bacon_constant_view_certification) \<and>
    \<not> (\<forall>F P.
      bacon_transition_certified_unary F \<longrightarrow>
      bacon_certified_proposition P \<longrightarrow>
      bacon_certified_proposition (F P))"
  using bacon_transition_constant_certified
    bacon_transition_view_not_pure
    bacon_transition_certified_unary_QSS
    bacon_transition_diagonal_actual_QLN
    bacon_transition_stock_not_application_closed
  by blast

locale bacon_certified_unary =
  fixes certified :: "bacon_prop_operator \<Rightarrow> bool"
  assumes certified_QSS_at_generic_r:
    "certified F \<Longrightarrow> certified G \<Longrightarrow>
      F bacon_generic_r = G bacon_generic_r \<Longrightarrow> F = G"
begin

theorem QSS_forbids_certifying_both_collision_operators:
  "\<not> (certified bacon_universal_test_operator \<and>
    certified bacon_false_operator)"
  using certified_QSS_at_generic_r
    bacon_universal_test_operator_distinct
  by auto

corollary universal_test_not_certified_if_false_is:
  assumes "certified bacon_false_operator"
  shows "\<not> certified bacon_universal_test_operator"
  using assms QSS_forbids_certifying_both_collision_operators by blast

end

section \<open>Exact semantic obligations for the PP target\<close>

context vector_equivalence_structure
begin

definition pp_action_model_obligations :: bool where
  "pp_action_model_obligations \<longleftrightarrow>
    (\<forall>A \<in> pp_purity_schema. valid_in_context [] A) \<and>
    (\<forall>A \<in> pp_application_closure_schema. valid_in_context [] A) \<and>
    valid_in_context [] pp_target_PP \<and>
    valid_in_context [] (pp_unique_fundamental Prop) \<and>
    (\<forall>A \<in> pp_no_other_fundamentals_schema.
      valid_in_context [] A) \<and>
    valid_in_context [] pp_zeroary_QLN \<and>
    valid_in_context [] pp_unary_QLN"

lemma pp_action_model_obligations_target_valid:
  assumes "pp_action_model_obligations"
  shows "\<forall>A \<in> pp_full_QLN_axioms. valid_in_context [] A"
  using assms
  unfolding pp_action_model_obligations_def pp_full_QLN_axioms_def
    pp_core_axioms_def
  by blast

theorem pp_consistency_from_action_model_obligations:
  assumes "pp_action_model_obligations"
  shows "pp_consistency_question"
proof (rule pp_consistency_from_concrete_model)
  fix A
  assume "A \<in> pp_full_QLN_axioms"
  then show "valid_in_context [] A"
    using assms pp_action_model_obligations_target_valid by blast
qed

end

end
