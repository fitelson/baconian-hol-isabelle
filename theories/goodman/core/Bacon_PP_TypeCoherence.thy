theory Bacon_PP_TypeCoherence
  imports Bacon_PP_TreeAut_Functions
begin

section \<open>A type-indexed coherence structure for tree conjugation\<close>

text \<open>
  \<open>Bacon_PP_TreeAut_Functions\<close> proves the domain and application obligations at the
  single type \<open>t \<rightarrow> t\<close>.  The remaining obligations --- higher-type equality, the
  quantifier domains, and the recursive all-type diagram --- cannot be stated at one
  fixed type.  This theory carries the recursion on Bacon types by Isabelle's own type
  structure, using a type class whose instances are generated from a base type by the
  function-space instance.  Every object-language type is then a HOL type in the class,
  and a class-level theorem is a theorem about every object-language type.

  The decisive design choice is that the class does \emph{not} carry the monoid action.
  Tree conjugation famously fails to commute with the action, so an action-based class
  could not have a coherent conjugation.  What conjugation does preserve is the family
  of \emph{local equivalences} the action induces, and that family is enough to define
  higher-type equality, the quantifier domains, and Bacon's local function spaces.
\<close>

subsection \<open>The class\<close>

class pp_dom =
  fixes pp_carrier :: "'a set"
    and pp_eqv :: "pp_word \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
    and pp_conj :: "'a \<Rightarrow> 'a"
  assumes pp_eqv_refl: "pp_eqv i x x"
    and pp_eqv_sym: "pp_eqv i x y \<Longrightarrow> pp_eqv i y x"
    and pp_eqv_trans:
      "pp_eqv i x y \<Longrightarrow> pp_eqv i y z \<Longrightarrow> pp_eqv i x z"
    and pp_eqv_mono: "pp_eqv i x y \<Longrightarrow> pp_eqv (k @ i) x y"
    and pp_conj_involution: "pp_conj (pp_conj x) = x"
    and pp_conj_carrier:
      "x \<in> pp_carrier \<Longrightarrow> pp_conj x \<in> pp_carrier"
    and pp_conj_key:
      "x \<in> pp_carrier \<Longrightarrow> y \<in> pp_carrier \<Longrightarrow>
        pp_eqv i (pp_conj x) (pp_conj y) = pp_eqv (pp_tw i) x y"
begin

text \<open>
  \<open>pp_eqv []\<close> is equality as far as the carrier can see.  Conjugation-fixedness is
  therefore stated with \<open>pp_eqv []\<close> rather than with HOL equality: at a function type
  two carrier members that agree on the carrier may still differ off it, and no
  object-language term can tell them apart.
\<close>

definition pp_fixed :: "'a \<Rightarrow> bool" where
  "pp_fixed x \<longleftrightarrow> pp_eqv [] (pp_conj x) x"

lemma pp_conj_key_root:
  assumes "x \<in> pp_carrier" and "y \<in> pp_carrier"
  shows "pp_eqv [] (pp_conj x) (pp_conj y) = pp_eqv [] x y"
  using pp_conj_key[OF assms, of "[]"] by simp

lemma pp_conj_carrier_image:
  "pp_conj ` pp_carrier = pp_carrier"
proof
  show "pp_conj ` pp_carrier \<subseteq> pp_carrier"
    using pp_conj_carrier by blast
next
  show "pp_carrier \<subseteq> pp_conj ` pp_carrier"
  proof
    fix x
    assume x: "x \<in> pp_carrier"
    then have "pp_conj x \<in> pp_carrier"
      by (rule pp_conj_carrier)
    moreover have "x = pp_conj (pp_conj x)"
      by (simp add: pp_conj_involution)
    ultimately show "x \<in> pp_conj ` pp_carrier"
      by blast
  qed
qed

lemma pp_conj_bij_carrier:
  "bij_betw pp_conj pp_carrier pp_carrier"
  unfolding bij_betw_def
proof
  show "inj_on pp_conj pp_carrier"
    by (metis inj_onI pp_conj_involution)
next
  show "pp_conj ` pp_carrier = pp_carrier"
    by (rule pp_conj_carrier_image)
qed

lemma pp_fixed_conj:
  assumes "pp_fixed x"
  shows "pp_eqv [] (pp_conj x) x"
  using assms unfolding pp_fixed_def .

text \<open>
  Reindexing a bounded quantifier along the conjugation.  This is the step that makes
  quantifier domains survive conjugation.
\<close>

lemma pp_conj_ball:
  "(\<forall>x \<in> pp_carrier. P (pp_conj x)) \<longleftrightarrow>
    (\<forall>y \<in> pp_carrier. P y)"
proof
  assume shifted: "\<forall>x \<in> pp_carrier. P (pp_conj x)"
  show "\<forall>y \<in> pp_carrier. P y"
  proof
    fix y
    assume y: "y \<in> pp_carrier"
    then have "pp_conj y \<in> pp_carrier"
      by (rule pp_conj_carrier)
    then have "P (pp_conj (pp_conj y))"
      using shifted by blast
    then show "P y"
      by (simp add: pp_conj_involution)
  qed
next
  assume plain: "\<forall>y \<in> pp_carrier. P y"
  show "\<forall>x \<in> pp_carrier. P (pp_conj x)"
    using plain pp_conj_carrier by blast
qed

lemma pp_conj_bex:
  "(\<exists>x \<in> pp_carrier. P (pp_conj x)) \<longleftrightarrow>
    (\<exists>y \<in> pp_carrier. P y)"
proof
  assume "\<exists>x \<in> pp_carrier. P (pp_conj x)"
  then show "\<exists>y \<in> pp_carrier. P y"
    using pp_conj_carrier by blast
next
  assume "\<exists>y \<in> pp_carrier. P y"
  then obtain y where y: "y \<in> pp_carrier" and Py: "P y"
    by blast
  have "pp_conj y \<in> pp_carrier"
    using y by (rule pp_conj_carrier)
  moreover have "P (pp_conj (pp_conj y))"
    using Py by (simp add: pp_conj_involution)
  ultimately show "\<exists>x \<in> pp_carrier. P (pp_conj x)"
    by blast
qed

end

subsection \<open>The propositional base type\<close>

datatype pp_base = PB (pp_un: pp_sem_prop)

lemma pp_base_eqI:
  "pp_un x = pp_un y \<Longrightarrow> x = y"
  by (cases x, cases y) simp

instantiation pp_base :: pp_dom
begin

definition pp_carrier_pp_base :: "pp_base set" where
  "pp_carrier_pp_base = UNIV"

definition pp_eqv_pp_base ::
    "pp_word \<Rightarrow> pp_base \<Rightarrow> pp_base \<Rightarrow> bool" where
  "pp_eqv_pp_base i x y \<longleftrightarrow>
    pp_view i (pp_un x) = pp_view i (pp_un y)"

definition pp_conj_pp_base :: "pp_base \<Rightarrow> pp_base" where
  "pp_conj_pp_base x = PB (pp_img (pp_un x))"

instance
proof
  fix i :: pp_word and x y z :: pp_base and k :: pp_word
  show "pp_eqv i x x"
    by (simp add: pp_eqv_pp_base_def)
  show "pp_eqv i x y \<Longrightarrow> pp_eqv i y x"
    by (simp add: pp_eqv_pp_base_def)
  show "pp_eqv i x y \<Longrightarrow> pp_eqv i y z \<Longrightarrow> pp_eqv i x z"
    by (simp add: pp_eqv_pp_base_def)
  show "pp_eqv i x y \<Longrightarrow> pp_eqv (k @ i) x y"
  proof -
    assume "pp_eqv i x y"
    then have "pp_view i (pp_un x) = pp_view i (pp_un y)"
      by (simp add: pp_eqv_pp_base_def)
    then have "pp_view k (pp_view i (pp_un x)) =
        pp_view k (pp_view i (pp_un y))"
      by simp
    then show "pp_eqv (k @ i) x y"
      by (simp add: pp_eqv_pp_base_def pp_view_compose)
  qed
  show "pp_conj (pp_conj x) = x"
    by (simp add: pp_conj_pp_base_def)
  show "x \<in> pp_carrier \<Longrightarrow> pp_conj x \<in> pp_carrier"
    by (simp add: pp_carrier_pp_base_def)
  show "x \<in> pp_carrier \<Longrightarrow> y \<in> pp_carrier \<Longrightarrow>
      pp_eqv i (pp_conj x) (pp_conj y) = pp_eqv (pp_tw i) x y"
    using pp_img_cone_equal_iff[of i "pp_un x" "pp_un y"]
    by (simp add: pp_eqv_pp_base_def pp_conj_pp_base_def
        pp_cone_equal_def)
qed

end

lemma pp_eqv_base_iff:
  "pp_eqv i x y \<longleftrightarrow>
    pp_view i (pp_un x) = pp_view i (pp_un y)"
  by (simp add: pp_eqv_pp_base_def)

lemma PB_pp_un[simp]: "PB (pp_un x) = x"
  by (cases x) simp

lemma pp_eqv_base_root_iff:
  "pp_eqv ([] :: pp_word) (x :: pp_base) y \<longleftrightarrow> x = y"
proof
  assume "pp_eqv ([] :: pp_word) x y"
  then have "pp_un x = pp_un y"
    by (simp add: pp_eqv_base_iff)
  then show "x = y" by (rule pp_base_eqI)
next
  assume "x = y"
  then show "pp_eqv ([] :: pp_word) x y"
    by (simp add: pp_eqv_base_iff)
qed

lemma pp_carrier_base[simp]:
  "(x :: pp_base) \<in> pp_carrier"
  by (simp add: pp_carrier_pp_base_def)

lemma pp_carrier_base_UNIV:
  "(pp_carrier :: pp_base set) = UNIV"
  by (simp add: pp_carrier_pp_base_def)

lemma pp_conj_base_un[simp]:
  "pp_un (pp_conj x) = pp_img (pp_un x)"
  by (simp add: pp_conj_pp_base_def)

lemma pp_fixed_base_iff:
  "pp_fixed (x :: pp_base) \<longleftrightarrow> pp_img (pp_un x) = pp_un x"
proof -
  have "pp_fixed x \<longleftrightarrow> pp_conj x = x"
    by (simp add: pp_fixed_def pp_eqv_base_root_iff)
  also have "... \<longleftrightarrow> PB (pp_img (pp_un x)) = x"
    by (simp add: pp_conj_pp_base_def)
  also have "... \<longleftrightarrow> pp_img (pp_un x) = pp_un x"
    by (cases x) simp
  finally show ?thesis .
qed

subsection \<open>The function-space instance\<close>

text \<open>
  The carrier at an exponential type is Bacon's local function domain: those functions
  that respect every local equivalence and stay inside the carrier.  The local
  equivalence at an exponential type is pointwise local equivalence over the carrier.
  Lemma \<open>pp_eqv_fun_base_iff_fun_view\<close> below checks that at the concrete type
  \<open>t \<rightarrow> t\<close> this coincides with equality of Bacon's own action \<open>pp_fun_view\<close>, so
  nothing has been quietly replaced.
\<close>

instantiation "fun" :: (pp_dom, pp_dom) pp_dom
begin

definition pp_carrier_fun :: "('a \<Rightarrow> 'b) set" where
  "pp_carrier_fun =
    {F. (\<forall>x \<in> pp_carrier. F x \<in> pp_carrier) \<and>
        (\<forall>i x y. x \<in> pp_carrier \<longrightarrow> y \<in> pp_carrier \<longrightarrow>
          pp_eqv i x y \<longrightarrow> pp_eqv i (F x) (F y))}"

definition pp_eqv_fun ::
    "pp_word \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "pp_eqv_fun i F G \<longleftrightarrow>
    (\<forall>x \<in> pp_carrier. pp_eqv i (F x) (G x))"

definition pp_conj_fun :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b)" where
  "pp_conj_fun F = (\<lambda>x. pp_conj (F (pp_conj x)))"

instance
proof
  fix i k :: pp_word and F G H :: "'a \<Rightarrow> 'b"
  show "pp_eqv i F F"
    by (simp add: pp_eqv_fun_def pp_eqv_refl)
  show "pp_eqv i F G \<Longrightarrow> pp_eqv i G F"
    by (simp add: pp_eqv_fun_def pp_eqv_sym)
  show "pp_eqv i F G \<Longrightarrow> pp_eqv i G H \<Longrightarrow> pp_eqv i F H"
    by (meson pp_eqv_fun_def pp_eqv_trans)
  show "pp_eqv i F G \<Longrightarrow> pp_eqv (k @ i) F G"
    by (simp add: pp_eqv_fun_def pp_eqv_mono)
  show "pp_conj (pp_conj F) = F"
    by (rule ext) (simp add: pp_conj_fun_def pp_conj_involution)
  show "F \<in> pp_carrier \<Longrightarrow> pp_conj F \<in> pp_carrier"
  proof -
    assume member: "F \<in> pp_carrier"
    have maps:
        "pp_conj (F (pp_conj x)) \<in> pp_carrier"
      if x: "x \<in> pp_carrier" for x
    proof -
      have "pp_conj x \<in> pp_carrier"
        using x by (rule pp_conj_carrier)
      then have "F (pp_conj x) \<in> pp_carrier"
        using member by (simp add: pp_carrier_fun_def)
      then show ?thesis by (rule pp_conj_carrier)
    qed
    have congruent:
        "\<And>j x y. x \<in> pp_carrier \<Longrightarrow> y \<in> pp_carrier \<Longrightarrow>
          pp_eqv j x y \<Longrightarrow>
          pp_eqv j (pp_conj (F (pp_conj x))) (pp_conj (F (pp_conj y)))"
    proof -
      fix j and x y :: 'a
      assume x: "x \<in> pp_carrier" and y: "y \<in> pp_carrier"
        and eqv: "pp_eqv j x y"
      have conj_x: "pp_conj x \<in> pp_carrier"
        using x by (rule pp_conj_carrier)
      have conj_y: "pp_conj y \<in> pp_carrier"
        using y by (rule pp_conj_carrier)
      have shifted: "pp_eqv (pp_tw j) (pp_conj x) (pp_conj y)"
        using pp_conj_key[OF x y, of "pp_tw j"] eqv by simp
      have image_eqv:
          "pp_eqv (pp_tw j) (F (pp_conj x)) (F (pp_conj y))"
        using member conj_x conj_y shifted
        by (simp add: pp_carrier_fun_def)
      have targets:
          "F (pp_conj x) \<in> pp_carrier" "F (pp_conj y) \<in> pp_carrier"
        using member conj_x conj_y by (simp_all add: pp_carrier_fun_def)
      show "pp_eqv j (pp_conj (F (pp_conj x))) (pp_conj (F (pp_conj y)))"
        using pp_conj_key[OF targets, of j] image_eqv by simp
    qed
    show "pp_conj F \<in> pp_carrier"
      using maps congruent
      by (auto simp: pp_carrier_fun_def pp_conj_fun_def)
  qed
  show "F \<in> pp_carrier \<Longrightarrow> G \<in> pp_carrier \<Longrightarrow>
      pp_eqv i (pp_conj F) (pp_conj G) = pp_eqv (pp_tw i) F G"
  proof -
    assume F: "F \<in> pp_carrier" and G: "G \<in> pp_carrier"
    have step:
        "pp_eqv i (pp_conj F) (pp_conj G) \<longleftrightarrow>
         (\<forall>x \<in> pp_carrier.
            pp_eqv (pp_tw i) (F (pp_conj x)) (G (pp_conj x)))"
    proof -
      have pointwise:
          "\<And>x. x \<in> pp_carrier \<Longrightarrow>
            pp_eqv i (pp_conj (F (pp_conj x))) (pp_conj (G (pp_conj x))) =
            pp_eqv (pp_tw i) (F (pp_conj x)) (G (pp_conj x))"
      proof -
        fix x :: 'a
        assume x: "x \<in> pp_carrier"
        have conj_x: "pp_conj x \<in> pp_carrier"
          using x by (rule pp_conj_carrier)
        have targets:
            "F (pp_conj x) \<in> pp_carrier" "G (pp_conj x) \<in> pp_carrier"
          using F G conj_x by (simp_all add: pp_carrier_fun_def)
        show "pp_eqv i (pp_conj (F (pp_conj x))) (pp_conj (G (pp_conj x))) =
            pp_eqv (pp_tw i) (F (pp_conj x)) (G (pp_conj x))"
          by (rule pp_conj_key[OF targets])
      qed
      show ?thesis
        using pointwise by (simp add: pp_eqv_fun_def pp_conj_fun_def)
    qed
    have reindex:
        "(\<forall>x \<in> pp_carrier.
            pp_eqv (pp_tw i) (F (pp_conj x)) (G (pp_conj x))) \<longleftrightarrow>
         (\<forall>w \<in> pp_carrier. pp_eqv (pp_tw i) (F w) (G w))"
      by (rule pp_conj_ball)
    show "pp_eqv i (pp_conj F) (pp_conj G) = pp_eqv (pp_tw i) F G"
      using step reindex by (simp add: pp_eqv_fun_def)
  qed
qed

end

lemma pp_carrier_fun_iff:
  "F \<in> pp_carrier \<longleftrightarrow>
    ((\<forall>x \<in> pp_carrier. F x \<in> pp_carrier) \<and>
     (\<forall>i x y. x \<in> pp_carrier \<longrightarrow> y \<in> pp_carrier \<longrightarrow>
        pp_eqv i x y \<longrightarrow> pp_eqv i (F x) (F y)))"
  by (simp add: pp_carrier_fun_def)

lemma pp_eqv_fun_iff:
  "pp_eqv i F G \<longleftrightarrow>
    (\<forall>x \<in> pp_carrier. pp_eqv i (F x) (G x))"
  by (simp add: pp_eqv_fun_def)

lemma pp_conj_fun_apply:
  "pp_conj F x = pp_conj (F (pp_conj x))"
  by (simp add: pp_conj_fun_def)

lemma pp_carrier_funI:
  assumes maps: "\<And>x. x \<in> pp_carrier \<Longrightarrow> F x \<in> pp_carrier"
    and cong: "\<And>i x y. x \<in> pp_carrier \<Longrightarrow> y \<in> pp_carrier \<Longrightarrow>
      pp_eqv i x y \<Longrightarrow> pp_eqv i (F x) (F y)"
  shows "F \<in> pp_carrier"
  using assms by (simp add: pp_carrier_fun_iff)

lemma pp_carrier_funD_maps:
  "F \<in> pp_carrier \<Longrightarrow> x \<in> pp_carrier \<Longrightarrow> F x \<in> pp_carrier"
  by (simp add: pp_carrier_fun_iff)

lemma pp_carrier_funD_cong:
  "F \<in> pp_carrier \<Longrightarrow> x \<in> pp_carrier \<Longrightarrow> y \<in> pp_carrier \<Longrightarrow>
    pp_eqv i x y \<Longrightarrow> pp_eqv i (F x) (F y)"
  by (simp add: pp_carrier_fun_iff)

subsection \<open>Coincidence with Bacon's own function-space action\<close>

text \<open>
  Nothing has been quietly replaced.  At the concrete type \<open>t \<rightarrow> t\<close> the class carrier
  is exactly Bacon's local function domain, the class equivalence is exactly equality
  of Bacon's own action \<open>pp_fun_view\<close>, and the class conjugation is exactly
  \<open>pp_tree_conjugate\<close>.
\<close>

definition pb_down ::
    "(pp_base \<Rightarrow> pp_base) \<Rightarrow> (pp_sem_prop \<Rightarrow> pp_sem_prop)" where
  "pb_down F = (\<lambda>P. pp_un (F (PB P)))"

definition pb_up ::
    "(pp_sem_prop \<Rightarrow> pp_sem_prop) \<Rightarrow> (pp_base \<Rightarrow> pp_base)" where
  "pb_up f = (\<lambda>x. PB (f (pp_un x)))"

lemma pb_down_up[simp]: "pb_down (pb_up f) = f"
  by (rule ext) (simp add: pb_down_def pb_up_def)

lemma pb_up_down[simp]: "pb_up (pb_down F) = F"
  by (rule ext) (simp add: pb_down_def pb_up_def)

theorem pp_carrier_fun_base_iff:
  "(F :: pp_base \<Rightarrow> pp_base) \<in> pp_carrier \<longleftrightarrow>
    pp_function_space_member (pb_down F)"
proof
  assume member: "F \<in> pp_carrier"
  show "pp_function_space_member (pb_down F)"
    unfolding pp_function_space_member_def
  proof (intro allI impI)
    fix i P Q
    assume views: "pp_view i P = pp_view i Q"
    have "pp_eqv i (PB P) (PB Q)"
      by (simp add: pp_eqv_base_iff views)
    then have "pp_eqv i (F (PB P)) (F (PB Q))"
      using member by (simp add: pp_carrier_fun_iff)
    then show "pp_view i (pb_down F P) = pp_view i (pb_down F Q)"
      by (simp add: pp_eqv_base_iff pb_down_def)
  qed
next
  assume member: "pp_function_space_member (pb_down F)"
  show "F \<in> pp_carrier"
  proof (rule pp_carrier_funI)
    fix x :: pp_base
    assume "x \<in> pp_carrier"
    show "F x \<in> pp_carrier" by simp
  next
    fix i and x y :: pp_base
    assume "x \<in> pp_carrier" and "y \<in> pp_carrier"
      and eqv: "pp_eqv i x y"
    have "pp_view i (pp_un x) = pp_view i (pp_un y)"
      using eqv by (simp add: pp_eqv_base_iff)
    then have "pp_view i (pb_down F (pp_un x)) =
        pp_view i (pb_down F (pp_un y))"
      using member unfolding pp_function_space_member_def by blast
    then show "pp_eqv i (F x) (F y)"
      by (simp add: pp_eqv_base_iff pb_down_def)
  qed
qed

theorem pp_eqv_fun_base_iff_fun_view:
  assumes F: "(F :: pp_base \<Rightarrow> pp_base) \<in> pp_carrier"
    and G: "G \<in> pp_carrier"
  shows "pp_eqv i F G \<longleftrightarrow>
    pp_fun_view i (pb_down F) = pp_fun_view i (pb_down G)"
proof
  assume eqv: "pp_eqv i F G"
  have pointwise:
      "pp_view i (pb_down F P) = pp_view i (pb_down G P)" for P
  proof -
    have "pp_eqv i (F (PB P)) (G (PB P))"
      using eqv by (simp add: pp_eqv_fun_iff)
    then show ?thesis
      by (simp add: pp_eqv_base_iff pb_down_def)
  qed
  show "pp_fun_view i (pb_down F) = pp_fun_view i (pb_down G)"
    by (rule ext) (simp add: pp_fun_view_apply pointwise)
next
  assume views:
      "pp_fun_view i (pb_down F) = pp_fun_view i (pb_down G)"
  have F_member: "pp_function_space_member (pb_down F)"
    using F by (simp add: pp_carrier_fun_base_iff)
  have G_member: "pp_function_space_member (pb_down G)"
    using G by (simp add: pp_carrier_fun_base_iff)
  have pointwise:
      "pp_view i (pb_down F X) = pp_view i (pb_down G X)" for X
  proof -
    have preimage:
        "pp_view i (pp_lift i (pp_view i X)) = pp_view i X"
      by simp
    have left: "pp_view i (pb_down F X) =
        pp_view i (pb_down F (pp_lift i (pp_view i X)))"
      using F_member preimage
      unfolding pp_function_space_member_def by blast
    have right: "pp_view i (pb_down G X) =
        pp_view i (pb_down G (pp_lift i (pp_view i X)))"
      using G_member preimage
      unfolding pp_function_space_member_def by blast
    have middle:
        "pp_view i (pb_down F (pp_lift i (pp_view i X))) =
         pp_view i (pb_down G (pp_lift i (pp_view i X)))"
      using views by (metis pp_fun_view_apply)
    show ?thesis using left right middle by simp
  qed
  show "pp_eqv i F G"
    unfolding pp_eqv_fun_iff
  proof (intro ballI)
    fix x :: pp_base
    assume "x \<in> pp_carrier"
    have "pp_view i (pb_down F (pp_un x)) =
        pp_view i (pb_down G (pp_un x))"
      by (rule pointwise)
    then show "pp_eqv i (F x) (G x)"
      by (simp add: pp_eqv_base_iff pb_down_def)
  qed
qed

lemma pb_down_conj:
  "pb_down (pp_conj F) = pp_tree_conjugate (pb_down F)"
  by (rule ext)
    (simp add: pb_down_def pp_conj_fun_apply pp_tree_conjugate_def
      pp_conj_pp_base_def)

lemma pp_eqv_fun_base_root_iff:
  "pp_eqv ([] :: pp_word) (F :: pp_base \<Rightarrow> pp_base) G \<longleftrightarrow> F = G"
proof
  assume "pp_eqv ([] :: pp_word) F G"
  then have "\<And>x. F x = G x"
    by (simp add: pp_eqv_fun_iff pp_eqv_base_root_iff)
  then show "F = G" by (rule ext)
next
  assume "F = G"
  then show "pp_eqv ([] :: pp_word) F G"
    by (simp add: pp_eqv_refl)
qed

theorem pp_fixed_fun_base_iff:
  "pp_fixed (F :: pp_base \<Rightarrow> pp_base) \<longleftrightarrow>
    pp_tree_conjugate (pb_down F) = pb_down F"
proof -
  have "pp_fixed F \<longleftrightarrow> pp_conj F = F"
    by (simp add: pp_fixed_def pp_eqv_fun_base_root_iff)
  also have "... \<longleftrightarrow> pb_down (pp_conj F) = pb_down F"
    by (metis pb_up_down)
  also have "... \<longleftrightarrow> pp_tree_conjugate (pb_down F) = pb_down F"
    by (simp add: pb_down_conj)
  finally show ?thesis .
qed

subsection \<open>The logical constants\<close>

lemma pp_view_Compl[simp]:
  "pp_view i (- P) = - pp_view i P"
  by (auto simp: pp_view_def)

lemma pp_view_Int[simp]:
  "pp_view i (P \<inter> Q) = pp_view i P \<inter> pp_view i Q"
  by (auto simp: pp_view_def)

lemma pp_root_true_img[simp]:
  "pp_root_true (pp_img P) \<longleftrightarrow> pp_root_true P"
  by (simp add: pp_root_true_def)

definition pb_neg :: "pp_base \<Rightarrow> pp_base" where
  "pb_neg x = PB (- pp_un x)"

definition pb_and :: "pp_base \<Rightarrow> pp_base \<Rightarrow> pp_base" where
  "pb_and x y = PB (pp_un x \<inter> pp_un y)"

definition pb_box :: "pp_base \<Rightarrow> pp_base" where
  "pb_box x = PB (pp_sem_box (pp_un x))"

definition pb_id :: "'a::pp_dom \<Rightarrow> 'a \<Rightarrow> pp_base" where
  "pb_id x y = PB {i. pp_eqv i x y}"

definition pb_all :: "('a::pp_dom \<Rightarrow> pp_base) \<Rightarrow> pp_base" where
  "pb_all f = PB {i. \<forall>x \<in> pp_carrier. i \<in> pp_un (f x)}"

definition pb_ex :: "('a::pp_dom \<Rightarrow> pp_base) \<Rightarrow> pp_base" where
  "pb_ex f = PB {i. \<exists>x \<in> pp_carrier. i \<in> pp_un (f x)}"

text \<open>
  At the base type the identity constant is the project's own local identity
  proposition.
\<close>

lemma pb_id_base:
  "pb_id (x :: pp_base) y =
    PB (pp_operator_equal (pp_un x) (pp_un y))"
  by (simp add: pb_id_def pp_eqv_base_iff pp_operator_equal_def)

lemma pp_eqv_base_pointwise:
  "pp_eqv i x y \<longleftrightarrow>
    (\<forall>k. (k @ i \<in> pp_un x) = (k @ i \<in> pp_un y))"
  by (auto simp: pp_eqv_base_iff pp_view_def)

lemma pb_neg_carrier: "pb_neg \<in> pp_carrier"
  by (simp add: pp_carrier_fun_iff pp_eqv_base_iff pb_neg_def)

lemma pb_box_carrier: "pb_box \<in> pp_carrier"
  by (simp add: pp_carrier_fun_iff pp_eqv_base_iff pb_box_def
      pp_sem_box_equivariant)

lemma pb_and_carrier: "pb_and \<in> pp_carrier"
  by (simp add: pp_carrier_fun_iff pp_eqv_fun_iff pp_eqv_base_iff
      pb_and_def)

lemma pb_neg_fixed: "pp_fixed pb_neg"
  by (simp add: pp_fixed_def pp_eqv_fun_iff pp_eqv_base_root_iff
      pp_conj_fun_apply pp_conj_pp_base_def pb_neg_def pp_img_compl)

lemma pb_box_fixed: "pp_fixed pb_box"
  by (simp add: pp_fixed_def pp_eqv_fun_iff pp_eqv_base_root_iff
      pp_conj_fun_apply pp_conj_pp_base_def pb_box_def pp_img_box)

lemma pb_and_fixed: "pp_fixed pb_and"
  by (simp add: pp_fixed_def pp_eqv_fun_iff pp_eqv_base_root_iff
      pp_conj_fun_apply pp_conj_pp_base_def pb_and_def pp_img_inter)

theorem pb_id_carrier:
  "(pb_id :: 'a::pp_dom \<Rightarrow> 'a \<Rightarrow> pp_base) \<in> pp_carrier"
proof (rule pp_carrier_funI)
  fix x :: 'a
  assume x: "x \<in> pp_carrier"
  show "pb_id x \<in> pp_carrier"
    unfolding pp_carrier_fun_iff
  proof (intro conjI ballI allI impI)
    fix z :: 'a
    assume "z \<in> pp_carrier"
    show "pb_id x z \<in> pp_carrier" by simp
  next
    fix i and z w :: 'a
    assume "z \<in> pp_carrier" and "w \<in> pp_carrier"
      and eqv: "pp_eqv i z w"
    have "pp_eqv (k @ i) x z = pp_eqv (k @ i) x w" for k
      using eqv pp_eqv_mono[of i z w k] pp_eqv_sym pp_eqv_trans
      by blast
    then show "pp_eqv i (pb_id x z) (pb_id x w)"
      by (simp add: pp_eqv_base_pointwise pb_id_def)
  qed
next
  fix i and x y :: 'a
  assume "x \<in> pp_carrier" and "y \<in> pp_carrier"
    and eqv: "pp_eqv i x y"
  show "pp_eqv i (pb_id x) (pb_id y)"
    unfolding pp_eqv_fun_iff
  proof
    fix z :: 'a
    assume "z \<in> pp_carrier"
    have "pp_eqv (k @ i) x z = pp_eqv (k @ i) y z" for k
      using eqv pp_eqv_mono[of i x y k] pp_eqv_sym pp_eqv_trans
      by blast
    then show "pp_eqv i (pb_id x z) (pb_id y z)"
      by (simp add: pp_eqv_base_pointwise pb_id_def)
  qed
qed

text \<open>
  Higher-type identity is preserved by tree conjugation.  This is the first obligation
  left open by \<open>Bacon_PP_TreeAut_Functions\<close>, and the class proves it at every Bacon
  type at once.
\<close>

theorem pb_id_conjugate:
  assumes x: "(x :: 'a::pp_dom) \<in> pp_carrier"
    and y: "y \<in> pp_carrier"
  shows "pp_conj (pb_id (pp_conj x) (pp_conj y)) = pb_id x y"
proof -
  have img_set:
      "pp_img {i. pp_eqv i (pp_conj x) (pp_conj y)} =
       {i. pp_eqv i x y}"
  proof (rule set_eqI)
    fix w
    have "w \<in> pp_img {i. pp_eqv i (pp_conj x) (pp_conj y)} \<longleftrightarrow>
        pp_eqv (pp_tw w) (pp_conj x) (pp_conj y)"
      by simp
    also have "... \<longleftrightarrow> pp_eqv w x y"
      using pp_conj_key[OF x y, of "pp_tw w"] by simp
    finally show
        "w \<in> pp_img {i. pp_eqv i (pp_conj x) (pp_conj y)} \<longleftrightarrow>
         w \<in> {i. pp_eqv i x y}"
      by simp
  qed
  show ?thesis
    by (simp add: pp_conj_pp_base_def pb_id_def img_set)
qed

theorem pb_id_fixed:
  "pp_fixed (pb_id :: 'a::pp_dom \<Rightarrow> 'a \<Rightarrow> pp_base)"
  unfolding pp_fixed_def pp_eqv_fun_iff
proof (intro ballI)
  fix x y :: 'a
  assume x: "x \<in> pp_carrier" and y: "y \<in> pp_carrier"
  have "pp_conj pb_id x y =
      pp_conj (pb_id (pp_conj x) (pp_conj y))"
    by (simp add: pp_conj_fun_apply)
  also have "... = pb_id x y"
    using x y by (rule pb_id_conjugate)
  finally show "pp_eqv [] (pp_conj pb_id x y) (pb_id x y)"
    by (simp add: pp_eqv_refl)
qed

theorem pb_all_carrier:
  "(pb_all :: ('a::pp_dom \<Rightarrow> pp_base) \<Rightarrow> pp_base) \<in> pp_carrier"
proof (rule pp_carrier_funI)
  fix f :: "'a \<Rightarrow> pp_base"
  assume "f \<in> pp_carrier"
  show "pb_all f \<in> pp_carrier" by simp
next
  fix i and f g :: "'a \<Rightarrow> pp_base"
  assume "f \<in> pp_carrier" and "g \<in> pp_carrier"
    and eqv: "pp_eqv i f g"
  have pointwise:
      "\<And>x k. x \<in> pp_carrier \<Longrightarrow>
        (k @ i \<in> pp_un (f x)) = (k @ i \<in> pp_un (g x))"
    using eqv by (simp add: pp_eqv_fun_iff pp_eqv_base_pointwise)
  show "pp_eqv i (pb_all f) (pb_all g)"
    unfolding pp_eqv_base_pointwise pb_all_def
    using pointwise by auto
qed

theorem pb_ex_carrier:
  "(pb_ex :: ('a::pp_dom \<Rightarrow> pp_base) \<Rightarrow> pp_base) \<in> pp_carrier"
proof (rule pp_carrier_funI)
  fix f :: "'a \<Rightarrow> pp_base"
  assume "f \<in> pp_carrier"
  show "pb_ex f \<in> pp_carrier" by simp
next
  fix i and f g :: "'a \<Rightarrow> pp_base"
  assume "f \<in> pp_carrier" and "g \<in> pp_carrier"
    and eqv: "pp_eqv i f g"
  have pointwise:
      "\<And>x k. x \<in> pp_carrier \<Longrightarrow>
        (k @ i \<in> pp_un (f x)) = (k @ i \<in> pp_un (g x))"
    using eqv by (simp add: pp_eqv_fun_iff pp_eqv_base_pointwise)
  show "pp_eqv i (pb_ex f) (pb_ex g)"
    unfolding pp_eqv_base_pointwise pb_ex_def
    using pointwise by auto
qed

text \<open>
  Conjugation bijects every quantifier domain, so quantification at every Bacon type is
  conjugation-fixed.  This is the second obligation left open by
  \<open>Bacon_PP_TreeAut_Functions\<close>.
\<close>

theorem pb_all_fixed:
  "pp_fixed (pb_all :: ('a::pp_dom \<Rightarrow> pp_base) \<Rightarrow> pp_base)"
  unfolding pp_fixed_def
proof (unfold pp_eqv_fun_iff, intro ballI)
  fix f :: "'a \<Rightarrow> pp_base"
  assume f: "f \<in> pp_carrier"
  have reindex:
      "(\<forall>x \<in> pp_carrier. w \<in> pp_un (f (pp_conj x))) \<longleftrightarrow>
       (\<forall>y \<in> pp_carrier. w \<in> pp_un (f y))" for w
    by (rule pp_conj_ball)
  have unfolded:
      "pp_un (pp_conj (pb_all (pp_conj f))) =
       {w. \<forall>y \<in> pp_carrier. w \<in> pp_un (f y)}"
  proof -
    have "pp_un (pp_conj (pb_all (pp_conj f))) =
        pp_img {i. \<forall>x \<in> pp_carrier.
          i \<in> pp_img (pp_un (f (pp_conj x)))}"
      by (simp add: pp_conj_pp_base_def pb_all_def pp_conj_fun_apply)
    also have "... =
        {w. \<forall>x \<in> pp_carrier. w \<in> pp_un (f (pp_conj x))}"
      by auto
    also have "... = {w. \<forall>y \<in> pp_carrier. w \<in> pp_un (f y)}"
      using reindex by blast
    finally show ?thesis .
  qed
  have "pp_conj pb_all f = pp_conj (pb_all (pp_conj f))"
    by (simp add: pp_conj_fun_apply)
  also have "... = pb_all f"
    using unfolded by (simp add: pb_all_def pp_base_eqI)
  finally show "pp_eqv [] (pp_conj pb_all f) (pb_all f)"
    by (simp add: pp_eqv_refl)
qed

theorem pb_ex_fixed:
  "pp_fixed (pb_ex :: ('a::pp_dom \<Rightarrow> pp_base) \<Rightarrow> pp_base)"
  unfolding pp_fixed_def
proof (unfold pp_eqv_fun_iff, intro ballI)
  fix f :: "'a \<Rightarrow> pp_base"
  assume f: "f \<in> pp_carrier"
  have reindex:
      "(\<exists>x \<in> pp_carrier. w \<in> pp_un (f (pp_conj x))) \<longleftrightarrow>
       (\<exists>y \<in> pp_carrier. w \<in> pp_un (f y))" for w
    by (rule pp_conj_bex)
  have unfolded:
      "pp_un (pp_conj (pb_ex (pp_conj f))) =
       {w. \<exists>y \<in> pp_carrier. w \<in> pp_un (f y)}"
  proof -
    have "pp_un (pp_conj (pb_ex (pp_conj f))) =
        pp_img {i. \<exists>x \<in> pp_carrier.
          i \<in> pp_img (pp_un (f (pp_conj x)))}"
      by (simp add: pp_conj_pp_base_def pb_ex_def pp_conj_fun_apply)
    also have "... =
        {w. \<exists>x \<in> pp_carrier. w \<in> pp_un (f (pp_conj x))}"
      by auto
    also have "... = {w. \<exists>y \<in> pp_carrier. w \<in> pp_un (f y)}"
      using reindex by blast
    finally show ?thesis .
  qed
  have "pp_conj pb_ex f = pp_conj (pb_ex (pp_conj f))"
    by (simp add: pp_conj_fun_apply)
  also have "... = pb_ex f"
    using unfolded by (simp add: pb_ex_def pp_base_eqI)
  finally show "pp_eqv [] (pp_conj pb_ex f) (pb_ex f)"
    by (simp add: pp_eqv_refl)
qed

subsection \<open>Closure under application, and the combinators\<close>

text \<open>
  Conjugation-fixedness is closed under application, and the combinators \<open>S\<close> and
  \<open>K\<close> are fixed outright.  By combinatory completeness this is the induction on
  object-language terms: every closed term built from fixed constants denotes a fixed
  carrier element.
\<close>

theorem pp_fixed_app:
  assumes F_carrier: "(F :: 'a::pp_dom \<Rightarrow> 'b::pp_dom) \<in> pp_carrier"
    and F_fixed: "pp_fixed F"
    and x_carrier: "x \<in> pp_carrier"
    and x_fixed: "pp_fixed x"
  shows "pp_fixed (F x)"
proof -
  have conj_x: "pp_conj x \<in> pp_carrier"
    using x_carrier by (rule pp_conj_carrier)
  have step1: "pp_eqv [] (pp_conj (F (pp_conj x))) (F x)"
  proof -
    have "pp_eqv [] (pp_conj F x) (F x)"
      using F_fixed x_carrier
      by (simp add: pp_fixed_def pp_eqv_fun_iff)
    then show ?thesis by (simp add: pp_conj_fun_apply)
  qed
  have inner: "pp_eqv [] (F (pp_conj x)) (F x)"
    using F_carrier conj_x x_carrier x_fixed[unfolded pp_fixed_def]
    by (rule pp_carrier_funD_cong)
  have targets:
      "F (pp_conj x) \<in> pp_carrier" "F x \<in> pp_carrier"
    using F_carrier conj_x x_carrier
    by (simp_all add: pp_carrier_funD_maps)
  have step2:
      "pp_eqv [] (pp_conj (F (pp_conj x))) (pp_conj (F x))"
    using pp_conj_key_root[OF targets] inner by simp
  show ?thesis
    unfolding pp_fixed_def
    using step1 step2 pp_eqv_sym pp_eqv_trans by blast
qed

theorem pp_carrier_app:
  "(F :: 'a::pp_dom \<Rightarrow> 'b::pp_dom) \<in> pp_carrier \<Longrightarrow>
    x \<in> pp_carrier \<Longrightarrow> F x \<in> pp_carrier"
  by (rule pp_carrier_funD_maps)

definition pb_K :: "'a::pp_dom \<Rightarrow> 'b::pp_dom \<Rightarrow> 'a" where
  "pb_K x y = x"

definition pb_S ::
    "('a::pp_dom \<Rightarrow> 'b::pp_dom \<Rightarrow> 'c::pp_dom) \<Rightarrow>
      ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'c" where
  "pb_S f g x = f x (g x)"

theorem pb_K_carrier:
  "(pb_K :: 'a::pp_dom \<Rightarrow> 'b::pp_dom \<Rightarrow> 'a) \<in> pp_carrier"
  by (simp add: pp_carrier_fun_iff pp_eqv_fun_iff pb_K_def pp_eqv_refl)

theorem pb_K_conjugate:
  "pp_conj (pb_K :: 'a::pp_dom \<Rightarrow> 'b::pp_dom \<Rightarrow> 'a) = pb_K"
  by (rule ext, rule ext)
    (simp add: pp_conj_fun_apply pb_K_def pp_conj_involution)

theorem pb_S_carrier:
  "(pb_S :: ('a::pp_dom \<Rightarrow> 'b::pp_dom \<Rightarrow> 'c::pp_dom) \<Rightarrow>
     ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'c) \<in> pp_carrier"
proof (rule pp_carrier_funI)
  fix f :: "'a \<Rightarrow> 'b \<Rightarrow> 'c"
  assume f: "f \<in> pp_carrier"
  show "pb_S f \<in> pp_carrier"
  proof (rule pp_carrier_funI)
    fix g :: "'a \<Rightarrow> 'b"
    assume g: "g \<in> pp_carrier"
    show "pb_S f g \<in> pp_carrier"
    proof (rule pp_carrier_funI)
      fix x :: 'a
      assume x: "x \<in> pp_carrier"
      show "pb_S f g x \<in> pp_carrier"
        using f g x by (simp add: pb_S_def pp_carrier_funD_maps)
    next
      fix i and x y :: 'a
      assume x: "x \<in> pp_carrier" and y: "y \<in> pp_carrier"
        and eqv: "pp_eqv i x y"
      have fy: "f y \<in> pp_carrier"
        using f y by (rule pp_carrier_funD_maps)
      have gx: "g x \<in> pp_carrier"
        using g x by (rule pp_carrier_funD_maps)
      have gy: "g y \<in> pp_carrier"
        using g y by (rule pp_carrier_funD_maps)
      have outer: "pp_eqv i (f x) (f y)"
        using f x y eqv by (rule pp_carrier_funD_cong)
      have first: "pp_eqv i (f x (g x)) (f y (g x))"
        using outer gx by (simp add: pp_eqv_fun_iff)
      have inner: "pp_eqv i (g x) (g y)"
        using g x y eqv by (rule pp_carrier_funD_cong)
      have second: "pp_eqv i (f y (g x)) (f y (g y))"
        using fy gx gy inner by (rule pp_carrier_funD_cong)
      show "pp_eqv i (pb_S f g x) (pb_S f g y)"
        unfolding pb_S_def
        using first second by (rule pp_eqv_trans)
    qed
  next
    fix i and g h :: "'a \<Rightarrow> 'b"
    assume g: "g \<in> pp_carrier" and h: "h \<in> pp_carrier"
      and eqv: "pp_eqv i g h"
    show "pp_eqv i (pb_S f g) (pb_S f h)"
      unfolding pp_eqv_fun_iff
    proof (intro ballI)
      fix x :: 'a
      assume x: "x \<in> pp_carrier"
      have fx: "f x \<in> pp_carrier"
        using f x by (rule pp_carrier_funD_maps)
      have gx: "g x \<in> pp_carrier"
        using g x by (rule pp_carrier_funD_maps)
      have hx: "h x \<in> pp_carrier"
        using h x by (rule pp_carrier_funD_maps)
      have "pp_eqv i (g x) (h x)"
        using eqv x by (simp add: pp_eqv_fun_iff)
      then show "pp_eqv i (pb_S f g x) (pb_S f h x)"
        unfolding pb_S_def
        using fx gx hx by (simp add: pp_carrier_funD_cong)
    qed
  qed
next
  fix i and f f' :: "'a \<Rightarrow> 'b \<Rightarrow> 'c"
  assume f: "f \<in> pp_carrier" and f': "f' \<in> pp_carrier"
    and eqv: "pp_eqv i f f'"
  show "pp_eqv i (pb_S f) (pb_S f')"
    unfolding pp_eqv_fun_iff
  proof (intro ballI)
    fix g :: "'a \<Rightarrow> 'b" and x :: 'a
    assume g: "g \<in> pp_carrier" and x: "x \<in> pp_carrier"
    have gx: "g x \<in> pp_carrier"
      using g x by (rule pp_carrier_funD_maps)
    have "pp_eqv i (f x) (f' x)"
      using eqv x by (simp add: pp_eqv_fun_iff)
    then show "pp_eqv i (pb_S f g x) (pb_S f' g x)"
      unfolding pb_S_def
      using gx by (simp add: pp_eqv_fun_iff)
  qed
qed

theorem pb_S_conjugate:
  "pp_conj (pb_S :: ('a::pp_dom \<Rightarrow> 'b::pp_dom \<Rightarrow> 'c::pp_dom) \<Rightarrow>
     ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'c) = pb_S"
  by (rule ext, rule ext, rule ext)
    (simp add: pp_conj_fun_apply pb_S_def pp_conj_involution)

lemma pp_fixed_of_conj_eq:
  "pp_conj x = x \<Longrightarrow> pp_fixed x"
  by (simp add: pp_fixed_def pp_eqv_refl)

corollary pb_K_fixed:
  "pp_fixed (pb_K :: 'a::pp_dom \<Rightarrow> 'b::pp_dom \<Rightarrow> 'a)"
  using pb_K_conjugate by (rule pp_fixed_of_conj_eq)

corollary pb_S_fixed:
  "pp_fixed (pb_S :: ('a::pp_dom \<Rightarrow> 'b::pp_dom \<Rightarrow> 'c::pp_dom) \<Rightarrow>
     ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'c)"
  using pb_S_conjugate by (rule pp_fixed_of_conj_eq)

subsection \<open>Purity is not conjugation-fixed\<close>

definition pb_invariant :: "(pp_base \<Rightarrow> pp_base) \<Rightarrow> bool" where
  "pb_invariant F \<longleftrightarrow> pp_fun_invariant (pb_down F)"

definition pb_zero :: "pp_base \<Rightarrow> pp_base" where
  "pb_zero = pb_up pp_zero_op"

lemma pb_zero_down[simp]: "pb_down pb_zero = pp_zero_op"
  by (simp add: pb_zero_def)

lemma pp_zero_op_member: "pp_function_space_member pp_zero_op"
  using pp_zero_op_equivariant by (rule pp_equivariant_operator_member)

lemma pb_zero_carrier: "pb_zero \<in> pp_carrier"
  by (simp add: pp_carrier_fun_base_iff pp_zero_op_member)

lemma pb_zero_invariant: "pb_invariant pb_zero"
  by (simp add: pb_invariant_def
      pp_equivariant_operator_invariant[OF pp_zero_op_equivariant])

lemma pp_tree_conjugate_zero:
  "pp_tree_conjugate pp_zero_op = pp_tw_zero_op"
  by (rule ext)
    (simp add: pp_tree_conjugate_def pp_tw_zero_op_conjugate)

lemma pp_tw_zero_op_member: "pp_function_space_member pp_tw_zero_op"
  using pp_tree_conjugate_member[OF pp_zero_op_member]
  by (simp add: pp_tree_conjugate_zero)

lemma pp_tw_zero_op_not_invariant:
  "\<not> pp_fun_invariant pp_tw_zero_op"
  using pp_fun_invariant_iff_equivariant[OF pp_tw_zero_op_member]
    pp_tw_zero_op_not_equivariant
  by blast

lemma pb_zero_conj_carrier: "pp_conj pb_zero \<in> pp_carrier"
  using pb_zero_carrier by (rule pp_conj_carrier)

lemma pb_zero_conj_not_invariant:
  "\<not> pb_invariant (pp_conj pb_zero)"
  by (simp add: pb_invariant_def pb_down_conj pp_tree_conjugate_zero
      pp_tw_zero_op_not_invariant)

text \<open>
  The target non-definability theorem.  No conjugation-fixed element of the model at
  type \<open>(t \<rightarrow> t) \<rightarrow> t\<close> has root truth tracking invariance.  Combined with the
  closure results above, this says that Purity for unary propositional operators is
  not definable from conjugation-fixed constants --- in particular, not Pure-free
  definable.
\<close>

theorem pp_purity_not_conjugation_fixed:
  "\<nexists>Pure :: (pp_base \<Rightarrow> pp_base) \<Rightarrow> pp_base.
     Pure \<in> pp_carrier \<and> pp_fixed Pure \<and>
     (\<forall>F \<in> pp_carrier.
        pp_root_true (pp_un (Pure F)) = pb_invariant F)"
proof
  assume "\<exists>Pure :: (pp_base \<Rightarrow> pp_base) \<Rightarrow> pp_base.
     Pure \<in> pp_carrier \<and> pp_fixed Pure \<and>
     (\<forall>F \<in> pp_carrier.
        pp_root_true (pp_un (Pure F)) = pb_invariant F)"
  then obtain Pure :: "(pp_base \<Rightarrow> pp_base) \<Rightarrow> pp_base" where
    fixed: "pp_fixed Pure"
    and tracks: "\<forall>F \<in> pp_carrier.
        pp_root_true (pp_un (Pure F)) = pb_invariant F"
    by blast
  have step: "pp_conj (Pure (pp_conj pb_zero)) = Pure pb_zero"
  proof -
    have "pp_eqv [] (pp_conj Pure pb_zero) (Pure pb_zero)"
      using fixed pb_zero_carrier
      by (simp add: pp_fixed_def pp_eqv_fun_iff)
    then show ?thesis
      by (simp add: pp_conj_fun_apply pp_eqv_base_root_iff)
  qed
  have transfer:
      "pp_root_true (pp_un (Pure (pp_conj pb_zero))) =
       pp_root_true (pp_un (Pure pb_zero))"
    using step by (metis pp_conj_base_un pp_root_true_img)
  have false_side:
      "\<not> pp_root_true (pp_un (Pure (pp_conj pb_zero)))"
    using tracks pb_zero_conj_carrier pb_zero_conj_not_invariant
    by blast
  have true_side:
      "pp_root_true (pp_un (Pure pb_zero))"
    using tracks pb_zero_carrier pb_zero_invariant by blast
  show False
    using transfer false_side true_side by simp
qed

subsection \<open>Why the tree automorphism cannot refute base definability\<close>

text \<open>
  The previous theorem refutes Pure-free definability of invariance as a predicate on
  the whole domain at type \<open>t \<rightarrow> t\<close>.  It does \emph{not} refute the base-definability
  condition, and the following theorem says exactly why.  That condition quantifies
  over the loci \<open>{b. Y b is an invariant member of L}\<close>, where \<open>L\<close> is the stock of
  denotations of closed Pure-free terms of type \<open>t \<rightarrow> t\<close>.  Every member of \<open>L\<close> is
  conjugation-fixed, so membership in \<open>L\<close> cancels the effect of moving the parameter,
  and every such locus is automatically conjugation-stable.  Hence no symmetry of this
  kind can refute base definability, and the tree-automorphism route should not be
  listed as a live attack on it.
\<close>

theorem pp_stock_locus_conjugation_stable:
  fixes Y :: "pp_base \<Rightarrow> pp_base \<Rightarrow> pp_base"
    and L :: "(pp_base \<Rightarrow> pp_base) set"
  assumes Y_fixed: "pp_fixed Y"
    and L_fixed: "\<And>l. l \<in> L \<Longrightarrow> pp_conj l = l"
    and L_stable: "\<And>l. l \<in> L \<Longrightarrow> pp_conj l \<in> L"
  shows "(Y b \<in> L \<and> pb_invariant (Y b)) \<longleftrightarrow>
         (Y (pp_conj b) \<in> L \<and> pb_invariant (Y (pp_conj b)))"
proof -
  have move: "Y (pp_conj b) = pp_conj (Y b)"
  proof -
    have "pp_eqv [] (pp_conj Y b) (Y b)"
      using Y_fixed by (simp add: pp_fixed_def pp_eqv_fun_iff)
    then have "pp_conj (Y (pp_conj b)) = Y b"
      by (simp add: pp_conj_fun_apply pp_eqv_fun_base_root_iff)
    then show ?thesis
      by (metis pp_conj_involution)
  qed
  show ?thesis
  proof (cases "Y b \<in> L")
    case True
    then have "pp_conj (Y b) = Y b" by (rule L_fixed)
    then show ?thesis using move True by simp
  next
    case False
    have "pp_conj (Y b) \<notin> L"
    proof
      assume "pp_conj (Y b) \<in> L"
      then have "pp_conj (pp_conj (Y b)) \<in> L" by (rule L_stable)
      then show False using False by (simp add: pp_conj_involution)
    qed
    then show ?thesis using move False by simp
  qed
qed

corollary pp_pointwise_fixed_stock_is_stable:
  assumes "\<And>l. l \<in> L \<Longrightarrow> pp_conj (l :: pp_base \<Rightarrow> pp_base) = l"
  shows "\<And>l. l \<in> L \<Longrightarrow> pp_conj l \<in> L"
  using assms by metis

end
