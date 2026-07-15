theory Bacon_Syntax
  imports Bacon_Types
begin

section \<open>Object-language syntax\<close>

text \<open>
  Terms use de Bruijn indices. Thus \<open>Var 0\<close> names the nearest enclosing
  binder, \<open>Var 1\<close> the next one out, and so on. This makes alpha-equivalent
  expressions definitionally identical in the metalanguage.
\<close>

datatype oterm =
    Var nat
  | Const string otype
  | App oterm oterm
  | Lam otype oterm
  | Eq otype oterm oterm
  | Neg oterm
  | Conj oterm oterm
  | Disj oterm oterm
  | Imp oterm oterm
  | Forall otype oterm
  | Exists otype oterm

abbreviation ObjIff :: "oterm \<Rightarrow> oterm \<Rightarrow> oterm" (infixr "\<longleftrightarrow>\<^sub>o" 25) where
  "A \<longleftrightarrow>\<^sub>o B \<equiv> Conj (Imp A B) (Imp B A)"

definition ObjTrue :: oterm where
  "ObjTrue = Forall Prop (Imp (Var 0) (Var 0))"

definition ObjFalse :: oterm where
  "ObjFalse = Neg ObjTrue"

abbreviation ObjExists :: "otype \<Rightarrow> oterm \<Rightarrow> oterm" where
  "ObjExists \<equiv> Exists"

end
