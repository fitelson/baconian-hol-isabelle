theory Bacon_PP_TreeAut
  imports Bacon_PP_Uniform_Index Bacon_PP_Parity
begin

section \<open>A tree-automorphism culling test\<close>

text \<open>
  At the propositional level, root-truth is computed from Boolean structure
  and cone-agreement, and every accessibility-preserving permutation of worlds
  preserves that fragment.  Extending this observation through Bacon's
  higher-type domains, equality, and quantifiers requires a further coherence
  proof; it is not assumed in this theory.

  This group is strictly larger than the automorphism group of the M-set model:
  its elements need \emph{not} commute with the action.  \<open>pp_tw\<close> below is such
  an element: it is an automorphism of the frame, it commutes with the Boolean
  operations and with \<open>pp_sem_box\<close>, but it does not commute with
  \<open>pp_view\<close>, and it carries an invariant unary operator to a non-invariant one.

  The checked consequence is that invariance at type \<open>t \<rightarrow> t\<close> is not a
  tree-stable property.  This supplies a candidate non-definability argument,
  conditional on the higher-type coherence proof developed next in
  \<open>Bacon_PP_TreeAut_Functions\<close>.
\<close>

section \<open>A tree automorphism that does not commute with the action\<close>

definition pp_sw :: "nat \<Rightarrow> nat" where
  "pp_sw a = (if a = 0 then 1 else if a = 1 then 0 else a)"

lemma pp_sw_sw[simp]: "pp_sw (pp_sw a) = a"
  by (simp add: pp_sw_def)

fun pp_tw :: "pp_word \<Rightarrow> pp_word" where
  "pp_tw [] = []"
| "pp_tw (a # u) = (if u = [] then a else pp_sw a) # pp_tw u"

lemma pp_tw_length[simp]: "length (pp_tw w) = length w"
  by (induct w) auto

lemma pp_tw_nil_iff[simp]: "pp_tw w = [] \<longleftrightarrow> w = []"
  by (cases w) auto

lemma pp_tw_tw[simp]: "pp_tw (pp_tw w) = w"
proof (induct w)
  case Nil
  show ?case by simp
next
  case (Cons a u)
  show ?case
  proof (cases "u = []")
    case True
    then show ?thesis by simp
  next
    case False
    then have "pp_tw u \<noteq> []" by simp
    then show ?thesis using Cons False by simp
  qed
qed

lemma pp_tw_inj: "inj pp_tw"
  by (metis injI pp_tw_tw)

lemma pp_tw_surj: "surj pp_tw"
  by (metis surjI pp_tw_tw)

lemma pp_tw_append_suffix:
  "\<exists>u. pp_tw (v @ i) = u @ pp_tw i \<and> length u = length v"
proof (induct v)
  case Nil
  show ?case by simp
next
  case (Cons a v)
  then obtain u where u: "pp_tw (v @ i) = u @ pp_tw i"
      and len: "length u = length v" by blast
  let ?c = "if v @ i = [] then a else pp_sw a"
  have "pp_tw ((a # v) @ i) = (?c # u) @ pp_tw i"
    using u by simp
  moreover have "length (?c # u) = length (a # v)"
    using len by simp
  ultimately show ?case by blast
qed

lemma pp_tw_accessible_forward:
  assumes "pp_accessible i j"
  shows "pp_accessible (pp_tw i) (pp_tw j)"
proof -
  obtain k where k: "j = k @ i" using assms unfolding pp_accessible_def by blast
  obtain u where "pp_tw (k @ i) = u @ pp_tw i"
    using pp_tw_append_suffix by blast
  then show ?thesis
    using k unfolding pp_accessible_def by blast
qed

lemma pp_tw_accessible[simp]:
  "pp_accessible (pp_tw i) (pp_tw j) \<longleftrightarrow> pp_accessible i j"
proof
  assume "pp_accessible (pp_tw i) (pp_tw j)"
  then have "pp_accessible (pp_tw (pp_tw i)) (pp_tw (pp_tw j))"
    by (rule pp_tw_accessible_forward)
  then show "pp_accessible i j" by simp
next
  assume "pp_accessible i j"
  then show "pp_accessible (pp_tw i) (pp_tw j)"
    by (rule pp_tw_accessible_forward)
qed

definition pp_img :: "pp_sem_prop \<Rightarrow> pp_sem_prop" where
  "pp_img P = pp_tw ` P"

lemma pp_img_mem[simp]: "w \<in> pp_img P \<longleftrightarrow> pp_tw w \<in> P"
  unfolding pp_img_def by (metis image_iff pp_tw_tw)

lemma pp_img_img[simp]: "pp_img (pp_img P) = P"
  by auto

lemma pp_img_compl: "pp_img (- P) = - pp_img P"
  by auto

lemma pp_img_inter: "pp_img (P \<inter> Q) = pp_img P \<inter> pp_img Q"
  by auto

lemma pp_img_union: "pp_img (P \<union> Q) = pp_img P \<union> pp_img Q"
  by auto

theorem pp_img_box: "pp_img (pp_sem_box P) = pp_sem_box (pp_img P)"
proof (rule set_eqI)
  fix w
  have "w \<in> pp_img (pp_sem_box P) \<longleftrightarrow>
        (\<forall>j. pp_accessible (pp_tw w) j \<longrightarrow> j \<in> P)"
    by (simp add: pp_sem_box_accessible_iff)
  also have "... \<longleftrightarrow> (\<forall>j. pp_accessible (pp_tw w) (pp_tw j) \<longrightarrow> pp_tw j \<in> P)"
    by (metis pp_tw_tw)
  also have "... \<longleftrightarrow> (\<forall>j. pp_accessible w j \<longrightarrow> pp_tw j \<in> P)"
    by simp
  also have "... \<longleftrightarrow> w \<in> pp_sem_box (pp_img P)"
    by (simp add: pp_sem_box_accessible_iff)
  finally show "w \<in> pp_img (pp_sem_box P) \<longleftrightarrow> w \<in> pp_sem_box (pp_img P)" .
qed

section \<open>Invariance is not stable under the tree automorphism\<close>

definition pp_zero_op :: "pp_sem_prop \<Rightarrow> pp_sem_prop" where
  "pp_zero_op P = {i. 0 # i \<in> P}"

lemma pp_zero_op_equivariant: "pp_equivariant_operator pp_zero_op"
  by (auto simp: pp_equivariant_operator_def pp_zero_op_def pp_view_def)

definition pp_tw_zero_op :: "pp_sem_prop \<Rightarrow> pp_sem_prop" where
  "pp_tw_zero_op P = {j. (if j = [] then 0 else 1) # j \<in> P}"

lemma pp_tw_zero_op_conjugate:
  "pp_tw_zero_op P = pp_img (pp_zero_op (pp_img P))"
proof (rule set_eqI)
  fix j
  have "j \<in> pp_img (pp_zero_op (pp_img P)) \<longleftrightarrow>
        pp_tw (0 # pp_tw j) \<in> P"
    by (simp add: pp_zero_op_def)
  moreover have "pp_tw (0 # pp_tw j) = (if j = [] then 0 else 1) # j"
    by (simp add: pp_sw_def)
  ultimately show "j \<in> pp_tw_zero_op P \<longleftrightarrow>
                   j \<in> pp_img (pp_zero_op (pp_img P))"
    by (simp add: pp_tw_zero_op_def)
qed

theorem pp_tw_zero_op_not_equivariant:
  "\<not> pp_equivariant_operator pp_tw_zero_op"
proof
  assume equivariant: "pp_equivariant_operator pp_tw_zero_op"
  let ?P = "{[1,0::nat]}"
  have "pp_view [0] (pp_tw_zero_op ?P) = pp_tw_zero_op (pp_view [0] ?P)"
    using equivariant unfolding pp_equivariant_operator_def by blast
  moreover have "[] \<in> pp_view [0] (pp_tw_zero_op ?P)"
    by (simp add: pp_view_def pp_tw_zero_op_def)
  moreover have "[] \<notin> pp_tw_zero_op (pp_view [0] ?P)"
    by (simp add: pp_view_def pp_tw_zero_op_def)
  ultimately show False by simp
qed

corollary pp_invariance_not_tree_stable:
  "\<exists>F. pp_equivariant_operator F \<and>
       \<not> pp_equivariant_operator (\<lambda>P. pp_img (F (pp_img P)))"
proof (intro exI[of _ pp_zero_op] conjI)
  show "pp_equivariant_operator pp_zero_op"
    by (rule pp_zero_op_equivariant)
next
  have "(\<lambda>P. pp_img (pp_zero_op (pp_img P))) = pp_tw_zero_op"
    by (rule ext) (simp add: pp_tw_zero_op_conjugate)
  then show "\<not> pp_equivariant_operator (\<lambda>P. pp_img (pp_zero_op (pp_img P)))"
    using pp_tw_zero_op_not_equivariant by simp
qed


section \<open>Two consistency checks\<close>

text \<open>
  First: the depth classes used to refute FIN-base are tree-stable, so the
  refutation is untouched by the stronger culling group.
\<close>

theorem pp_img_level_class[simp]:
  "pp_img (pp_level_class p r) = pp_level_class p r"
  by (auto simp: pp_level_class_mem_iff)

corollary pp_img_level_partition:
  "pp_img ` pp_level_partition p = pp_level_partition p"
proof (rule set_eqI)
  fix X
  show "X \<in> pp_img ` pp_level_partition p \<longleftrightarrow>
        X \<in> pp_level_partition p"
  proof
    assume "X \<in> pp_img ` pp_level_partition p"
    then obtain Z where Z: "Z \<in> pp_level_partition p" and X: "X = pp_img Z"
      by blast
    obtain r where "Z = pp_level_class p r"
      using Z unfolding pp_level_partition_def by blast
    then show "X \<in> pp_level_partition p"
      using X Z by simp
  next
    assume X: "X \<in> pp_level_partition p"
    then obtain r where r: "X = pp_level_class p r"
      unfolding pp_level_partition_def by blast
    then have "pp_img X = X" by simp
    then show "X \<in> pp_img ` pp_level_partition p"
      using X by (metis image_eqI)
  qed
qed

text \<open>
  Second: \<open>pp_tw\<close> is a frame automorphism that does \emph{not} commute with the
  M-set action.  Thus it is not an automorphism of the M-set presentation.
\<close>

theorem pp_tw_does_not_commute_with_view:
  "\<exists>i P. pp_img (pp_view i P) \<noteq> pp_view (pp_tw i) (pp_img P)"
proof (intro exI[of _ "[0::nat]"] exI[of _ "{[1,0::nat]}"])
  have tw_one: "pp_tw [1::nat] = [1::nat]" by simp
  have tw_two: "pp_tw [1,0::nat] = [0,0::nat]" by (simp add: pp_sw_def)
  have left: "[1::nat] \<in> pp_img (pp_view [0::nat] {[1,0::nat]})"
    using tw_one by (simp add: pp_view_def)
  have right: "[1::nat] \<notin> pp_view (pp_tw [0::nat]) (pp_img {[1,0::nat]})"
    using tw_two by (simp add: pp_view_def)
  show "pp_img (pp_view [0::nat] {[1,0::nat]}) \<noteq>
        pp_view (pp_tw [0::nat]) (pp_img {[1,0::nat]})"
    using left right by blast
qed

text \<open>
  Reading.  \<open>pp_tw\<close> preserves \<open>\<box>\<close> and the Boolean operations but does not
  preserve invariance of unary operators under conjugation.  To infer the
  advertised Pure-free non-definability result, one must additionally show
  that conjugation preserves Bacon's higher-type domains, application,
  equality, and quantification.  The domain and application parts are proved
  in \<open>Bacon_PP_TreeAut_Functions\<close>; equality and the recursive all-type
  coherence remain open.
\<close>


section \<open>The parity orbit-constancy locus is not tree-stable\<close>

text \<open>
  The parity family \<open>Y' = \<lambda>b.\<lambda>c. \<box>(b \<leftrightarrow> c) \<or> \<box>(b \<leftrightarrow> \<not>c)\<close> has
  orbit-constancy locus \<open>{b. pp_orbit b \<subseteq> {b, -b}}\<close>.  That locus contains
  every parity proposition, but it is not stable under \<open>pp_tw\<close>.  Hence it is
  a candidate for a non-definability result once the higher-type coherence
  theorem is available.  The stock locus is contained in the four-element set
  \<open>{\<top>, \<bottom>, even-length, odd-length}\<close>.
\<close>

theorem pp_parity_locus_not_tree_stable:
  "pp_orbit (pp_parity {0}) \<subseteq> {pp_parity {0}, - pp_parity {0}} \<and>
   \<not> pp_orbit (pp_img (pp_parity {0}))
       \<subseteq> {pp_img (pp_parity {0}), - pp_img (pp_parity {0})}"
proof
  show "pp_orbit (pp_parity {0}) \<subseteq> {pp_parity {0}, - pp_parity {0}}"
    by (rule pp_parity_orbit_two)
next
  let ?c = "pp_img (pp_parity {0::nat})"
  have root_in: "[] \<in> ?c"
    by (simp add: pp_parity_def)
  have root_out: "[] \<notin> pp_view [0::nat] ?c"
    by (simp add: pp_view_def pp_parity_def)
  have one_in_c: "[1::nat] \<in> ?c"
    by (simp add: pp_parity_def)
  have one_in_view: "[1::nat] \<in> pp_view [0::nat] ?c"
    by (simp add: pp_view_def pp_parity_def pp_sw_def)
  have neq_c: "pp_view [0::nat] ?c \<noteq> ?c"
    using root_in root_out by blast
  have neq_compl: "pp_view [0::nat] ?c \<noteq> - ?c"
    using one_in_c one_in_view by blast
  have "pp_view [0::nat] ?c \<in> pp_orbit ?c"
    unfolding pp_orbit_def by blast
  then show "\<not> pp_orbit ?c \<subseteq> {?c, - ?c}"
    using neq_c neq_compl by blast
qed

end
