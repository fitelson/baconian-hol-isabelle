theory Bacon_Types
  imports Main
begin

section \<open>Object-language types\<close>

text \<open>
  These are the simple types of the object language, not Isabelle/HOL types.
  The base type \<open>Ind\<close> is for individuals and \<open>Prop\<close> is for propositions.
\<close>

datatype otype =
    Ind
  | Prop
  | Arr otype otype

notation Arr (infixr "\<rightarrow>\<^sub>o" 200)

fun order :: "otype \<Rightarrow> nat" where
  "order Ind = 0"
| "order Prop = 0"
| "order (\<sigma> \<rightarrow>\<^sub>o \<tau>) = max (Suc (order \<sigma>)) (order \<tau>)"

lemma order_nonzero_if_arrow:
  "order (\<sigma> \<rightarrow>\<^sub>o \<tau>) > 0"
  by simp

end

