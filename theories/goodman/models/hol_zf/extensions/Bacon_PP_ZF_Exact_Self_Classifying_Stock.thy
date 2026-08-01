theory Bacon_PP_ZF_Exact_Self_Classifying_Stock
  imports Bacon_PP_ZF_Exact_M1
begin

section \<open>Self-classifying enlargements on Bacon's exact carriers\<close>

definition pp_e_contains_closed_logical_stock ::
    "(otype \<Rightarrow> nat list \<Rightarrow> ZF \<Rightarrow> bool) \<Rightarrow> bool"
where
  "pp_e_contains_closed_logical_stock Pure \<longleftrightarrow>
    (\<forall>\<sigma> w x. pp_e_closed_logical_stock \<sigma> w x \<longrightarrow> Pure \<sigma> w x)"

definition pp_e_application_closed_stock ::
    "(otype \<Rightarrow> nat list \<Rightarrow> ZF \<Rightarrow> bool) \<Rightarrow> bool"
where
  "pp_e_application_closed_stock Pure \<longleftrightarrow>
    (\<forall>\<sigma> \<tau> w f x.
      Elem f (pp_e_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>)) \<longrightarrow>
      Elem x (pp_e_domain \<sigma>) \<longrightarrow>
      Pure (\<sigma> \<rightarrow>\<^sub>o \<tau>) w f \<longrightarrow>
      Pure \<sigma> w x \<longrightarrow>
      Pure \<tau> w (f \<acute> x))"

definition pp_e_self_classifying_stock ::
    "(otype \<Rightarrow> nat list \<Rightarrow> ZF \<Rightarrow> bool) \<Rightarrow> bool"
where
  "pp_e_self_classifying_stock Pure \<longleftrightarrow>
    (\<forall>\<sigma> w.
      Pure (\<sigma> \<rightarrow>\<^sub>o Prop) w
        (pp_e_classifier \<sigma> (Pure \<sigma>)))"

definition pp_e_exact_pure_stock_candidate ::
    "(otype \<Rightarrow> nat list \<Rightarrow> ZF \<Rightarrow> bool) \<Rightarrow> bool"
where
  "pp_e_exact_pure_stock_candidate Pure \<longleftrightarrow>
    (\<forall>\<sigma>. pp_e_predicate_admissible \<sigma> (Pure \<sigma>)) \<and>
    pp_e_contains_closed_logical_stock Pure \<and>
    pp_e_application_closed_stock Pure \<and>
    pp_e_self_classifying_stock Pure"

context pp_e_moving_internal_parameters
begin

lemma pp_e_purity_of_pure_holds_iff_self_classification:
  "pp_e_holds
      (pp_e_eval (pp_e_moving_internal_constants Pure) \<rho>
        (pp_purity_of_pure \<sigma>)) w
    \<longleftrightarrow>
    Pure (\<sigma> \<rightarrow>\<^sub>o Prop) w
      (pp_e_classifier \<sigma> (Pure \<sigma>))"
proof -
  have typed:
      "[] \<turnstile> pp_Pure \<sigma> : (\<sigma> \<rightarrow>\<^sub>o Prop)"
    by (rule typed_pp_Pure)
  have empty: "pp_e_env_typed [] \<rho>"
    by (simp add: pp_e_env_typed_def lookup_def)
  show ?thesis
    unfolding pp_purity_of_pure_def
    using pp_e_moving_eval_pure_holds[OF typed empty, of w]
    by simp
qed

theorem pp_e_purity_of_pure_gvalid_iff_self_classification:
  "MovingExactBaconConstants.ExactBaconHenkin.gvalid []
      (pp_purity_of_pure \<sigma>)
    \<longleftrightarrow>
    (\<forall>w. Pure (\<sigma> \<rightarrow>\<^sub>o Prop) w
      (pp_e_classifier \<sigma> (Pure \<sigma>)))"
proof
  assume valid:
      "MovingExactBaconConstants.ExactBaconHenkin.gvalid []
        (pp_purity_of_pure \<sigma>)"
  show "\<forall>w. Pure (\<sigma> \<rightarrow>\<^sub>o Prop) w
      (pp_e_classifier \<sigma> (Pure \<sigma>))"
  proof
    fix w
    have holds:
        "pp_e_holds
          (MovingExactBaconConstants.pp_e_den
            (pp_purity_of_pure \<sigma>) []) w"
      using MovingExactBaconConstants.ExactBaconHenkin.gvalidD[
        OF valid, of "[]" w] by simp
    show "Pure (\<sigma> \<rightarrow>\<^sub>o Prop) w
        (pp_e_classifier \<sigma> (Pure \<sigma>))"
      using holds
      unfolding MovingExactBaconConstants.pp_e_den_def
      using pp_e_purity_of_pure_holds_iff_self_classification by blast
  qed
next
  assume self:
      "\<forall>w. Pure (\<sigma> \<rightarrow>\<^sub>o Prop) w
        (pp_e_classifier \<sigma> (Pure \<sigma>))"
  show "MovingExactBaconConstants.ExactBaconHenkin.gvalid []
      (pp_purity_of_pure \<sigma>)"
  proof (rule MovingExactBaconConstants.ExactBaconHenkin.gvalidI)
    fix env w
    assume "env_ok (map pp_e_dom []) env"
    show "pp_e_holds
        (MovingExactBaconConstants.pp_e_den
          (pp_purity_of_pure \<sigma>) env) w"
      unfolding MovingExactBaconConstants.pp_e_den_def
      using pp_e_purity_of_pure_holds_iff_self_classification
        self by blast
  qed
qed

theorem pp_e_all_PP_instances_gvalid_iff_self_classifying:
  "(\<forall>\<sigma>.
      MovingExactBaconConstants.ExactBaconHenkin.gvalid []
        (pp_purity_of_pure \<sigma>))
    \<longleftrightarrow> pp_e_self_classifying_stock Pure"
  unfolding pp_e_self_classifying_stock_def
  by (simp add: pp_e_purity_of_pure_gvalid_iff_self_classification)

corollary pp_e_target_PP_gvalid_iff_unary_classifier_member:
  "MovingExactBaconConstants.ExactBaconHenkin.gvalid [] pp_target_PP
    \<longleftrightarrow>
    (\<forall>w. Pure
      ((Prop \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o Prop) w
      (pp_e_classifier (Prop \<rightarrow>\<^sub>o Prop)
        (Pure (Prop \<rightarrow>\<^sub>o Prop))))"
  unfolding pp_target_PP_def
  by (rule pp_e_purity_of_pure_gvalid_iff_self_classification)

theorem pp_e_closed_logical_purity_for_enlargement:
  assumes contains: "pp_e_contains_closed_logical_stock Pure"
    and typed: "[] \<turnstile> M : \<sigma>"
    and logical: "pp_logical_vocabulary M"
  shows "MovingExactBaconConstants.ExactBaconHenkin.gvalid \<Gamma>
    (pp_pure \<sigma> M)"
proof (rule MovingExactBaconConstants.ExactBaconHenkin.gvalidI)
  fix env w
  assume "env_ok (map pp_e_dom \<Gamma>) env"
  have stock:
      "pp_e_closed_logical_stock \<sigma> w
        (pp_e_eval (pp_e_moving_internal_constants Pure)
          (pp_e_list_env env) M)"
    using pp_e_closed_logical_stock_contains_eval[OF typed logical] .
  have pure:
      "Pure \<sigma> w
        (pp_e_eval (pp_e_moving_internal_constants Pure)
          (pp_e_list_env env) M)"
    using contains stock
    unfolding pp_e_contains_closed_logical_stock_def by blast
  have empty: "pp_e_env_typed [] (pp_e_list_env env)"
    by (simp add: pp_e_env_typed_def lookup_def)
  show "pp_e_holds
      (MovingExactBaconConstants.pp_e_den (pp_pure \<sigma> M) env) w"
    unfolding MovingExactBaconConstants.pp_e_den_def
    using pp_e_moving_eval_pure_holds[OF typed empty, of w] pure by blast
qed

theorem pp_e_application_closure_for_enlargement:
  assumes closed: "pp_e_application_closed_stock Pure"
  shows "MovingExactBaconConstants.ExactBaconHenkin.gvalid \<Gamma>
    (pp_application_closure \<sigma> \<tau>)"
proof (rule MovingExactBaconConstants.ExactBaconHenkin.gvalidI)
  fix env w
  assume "env_ok (map pp_e_dom \<Gamma>) env"
  show "pp_e_holds
      (MovingExactBaconConstants.pp_e_den
        (pp_application_closure \<sigma> \<tau>) env) w"
    unfolding MovingExactBaconConstants.pp_e_den_def
      pp_application_closure_def pp_pure_def
    using closed
    by (simp add: pp_e_classifier_holds pp_e_app_closed
        extend_env.simps pp_e_application_closed_stock_def)
qed

theorem pp_e_exact_candidate_validates_purity_closure_and_PP:
  assumes candidate: "pp_e_exact_pure_stock_candidate Pure"
  shows
    "(\<forall>\<sigma> M \<Gamma>.
        [] \<turnstile> M : \<sigma> \<longrightarrow>
        pp_logical_vocabulary M \<longrightarrow>
        MovingExactBaconConstants.ExactBaconHenkin.gvalid \<Gamma>
          (pp_pure \<sigma> M))
      \<and>
     (\<forall>\<sigma> \<tau> \<Gamma>.
        MovingExactBaconConstants.ExactBaconHenkin.gvalid \<Gamma>
          (pp_application_closure \<sigma> \<tau>))
      \<and>
     (\<forall>\<sigma>.
        MovingExactBaconConstants.ExactBaconHenkin.gvalid []
          (pp_purity_of_pure \<sigma>))"
proof -
  have contains: "pp_e_contains_closed_logical_stock Pure"
    and closed: "pp_e_application_closed_stock Pure"
    and self: "pp_e_self_classifying_stock Pure"
    using candidate unfolding pp_e_exact_pure_stock_candidate_def by auto
  show ?thesis
    using pp_e_closed_logical_purity_for_enlargement[OF contains]
      pp_e_application_closure_for_enlargement[OF closed]
      pp_e_all_PP_instances_gvalid_iff_self_classifying self
    by blast
qed

end


section \<open>The exact closed-logical stock\<close>

theorem pp_e_closed_logical_target_PP_iff_classifier_member:
  "GenericExactBaconConstants.ExactBaconHenkin.gvalid [] pp_target_PP
    \<longleftrightarrow>
    (\<forall>w.
      pp_e_closed_logical_stock
        ((Prop \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o Prop) w
        (pp_e_classifier (Prop \<rightarrow>\<^sub>o Prop)
          (pp_e_closed_logical_stock
            (Prop \<rightarrow>\<^sub>o Prop))))"
proof
  assume valid:
      "GenericExactBaconConstants.ExactBaconHenkin.gvalid [] pp_target_PP"
  show "\<forall>w.
      pp_e_closed_logical_stock
        ((Prop \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o Prop) w
        (pp_e_classifier (Prop \<rightarrow>\<^sub>o Prop)
          (pp_e_closed_logical_stock
            (Prop \<rightarrow>\<^sub>o Prop)))"
  proof
    fix w
    have holds:
        "pp_e_holds
          (GenericExactBaconConstants.pp_e_den pp_target_PP []) w"
      using GenericExactBaconConstants.ExactBaconHenkin.gvalidD[
        OF valid, of "[]" w] by simp
    show "pp_e_closed_logical_stock
        ((Prop \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o Prop) w
        (pp_e_classifier (Prop \<rightarrow>\<^sub>o Prop)
          (pp_e_closed_logical_stock
            (Prop \<rightarrow>\<^sub>o Prop)))"
      using holds
      unfolding GenericExactBaconConstants.pp_e_den_def
        pp_e_generic_target_PP_holds_iff .
  qed
next
  assume member:
      "\<forall>w.
        pp_e_closed_logical_stock
          ((Prop \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o Prop) w
          (pp_e_classifier (Prop \<rightarrow>\<^sub>o Prop)
            (pp_e_closed_logical_stock
              (Prop \<rightarrow>\<^sub>o Prop)))"
  show "GenericExactBaconConstants.ExactBaconHenkin.gvalid [] pp_target_PP"
  proof (rule GenericExactBaconConstants.ExactBaconHenkin.gvalidI)
    fix env w
    assume "env_ok (map pp_e_dom []) env"
    show "pp_e_holds
        (GenericExactBaconConstants.pp_e_den pp_target_PP env) w"
      unfolding GenericExactBaconConstants.pp_e_den_def
      using pp_e_generic_target_PP_holds_iff member by blast
  qed
qed

text \<open>
  No theorem below this point asserts either side of the last equivalence.
  In particular, the exact carrier construction does not by itself prove that
  the classifier is absent from the next closed-logical stock.
\<close>

end
