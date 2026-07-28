theory Bacon_PP_Fresh_Local_Henkin_Extension
  imports
    "Goodman_CEVplus.Bacon_CEV_Axiom_Extension"
    "Bacon_Classicism.Bacon_Clean_Completeness"
begin

section \<open>A first Henkin extension above added principles\<close>

text \<open>
  Let \<open>T\<close> be a finite, well-typed stock of additional principles.  If the
  CEV axiom extension by \<open>T\<close> is consistent, then \<open>T\<close> is also consistent
  when its members are treated as local assumptions.  The clean staged
  Henkin construction therefore produces a witnessed, locally maximal theory
  containing \<open>T\<close>.

  This theorem is deliberately limited.  The resulting theory contains the
  additional principles themselves, but the ordinary local construction does
  not yet ensure that it contains every result obtained by applying
  Generalization, Instantiation, vector Equivalence, or Necessitation above
  those principles.  That stronger closure is the relative Henkin problem
  addressed in the following theories.
\<close>

theorem CEV_axiom_consistent_clean_Henkin_extension:
  assumes finite_T: "finite T"
    and typed_T: "typed_theory \<Gamma> T"
    and consistent_T: "CEV_axiom_consistent \<Gamma> T"
  obtains U where
    "T \<subseteq> U"
    "CEV_clean_Henkin_theory \<Gamma> U"
proof -
  have local_T: "CEV_consistent \<Gamma> T"
    using consistent_T
    by (rule CEV_axiom_consistent_imp_local_consistent)

  obtain body_enum where
    body_enum: "enumerates_witness_bodies \<Gamma> body_enum"
    using enumerates_witness_bodies_exists by blast

  let ?S = "staged_henkin_extension \<Gamma> T body_enum"

  have T_sub_S: "T \<subseteq> ?S"
    by (rule staged_henkin_extension_extends)
  have typed_S: "typed_theory \<Gamma> ?S"
    using typed_T by (rule staged_henkin_extension_typed)
  have consistent_S: "CEV_consistent \<Gamma> ?S"
    using finite_T typed_T local_T
    by (rule CEV_staged_henkin_extension_consistent_clean)
  have available_S: "Henkin_witness_axioms_available \<Gamma> ?S"
    using body_enum
    by (rule staged_henkin_extension_witness_axioms_available)

  obtain formula_enum where
    formula_enum: "enumerates_formulas \<Gamma> formula_enum"
    using enumerates_formulas_exists by blast

  let ?U = "CEV_lindenbaum_extension \<Gamma> ?S formula_enum"

  have S_sub_U: "?S \<subseteq> ?U"
    by (rule CEV_lindenbaum_extension_extends)
  have maximal_U: "CEV_locally_maximal_consistent \<Gamma> ?U"
    using typed_S consistent_S formula_enum
    by (rule CEV_lindenbaum_extension_locally_maximal_consistent)
  have available_U: "Henkin_witness_axioms_available \<Gamma> ?U"
    using available_S S_sub_U
    by (rule Henkin_witness_axioms_available_mono)
  have witnessed_U: "Henkin_witnessed \<Gamma> ?U"
    using maximal_U available_U
    by (rule Henkin_witnessed_of_CEV_local_maximal_available_clean)
  have henkin_U: "CEV_clean_Henkin_theory \<Gamma> ?U"
    using maximal_U witnessed_U
    unfolding CEV_clean_Henkin_theory_def by blast
  have T_sub_U: "T \<subseteq> ?U"
    using T_sub_S S_sub_U by blast

  show ?thesis
    using that[OF T_sub_U henkin_U] .
qed

end
