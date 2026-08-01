theory Analysis
  imports Complex_Main
begin

section \<open>3.1 Definicije\<close>

(* mi22062_Nenad_Pesic_FORMULACIJA *)
type_synonym 'a sequence = "nat \<Rightarrow> 'a"

(* mi22062_Nenad_Pesic_FORMULACIJA *)
definition tendsto :: "(nat \<Rightarrow> 'a::metric_space) \<Rightarrow> 'a \<Rightarrow> bool" where
  "tendsto x a \<longleftrightarrow> (\<forall>\<epsilon>>0. \<exists>N. \<forall>n\<ge>N. dist (x n) a < \<epsilon>)"

(* mi22062_Nenad_Pesic_FORMULACIJA *)
definition bounded :: "(nat \<Rightarrow> 'a::metric_space) \<Rightarrow> bool" where
  "bounded x \<longleftrightarrow> (\<exists>p M. \<forall>n. dist (x n) p \<le> M)"

section \<open>Rudin 3.2 (b) -- Jedinstvenost granicne vrednosti\<close>

(* mi22062_Nenad_Pesic_FORMULACIJA *)
lemma tendsto_unique:
  fixes x :: "nat \<Rightarrow> 'a::metric_space"
  assumes "tendsto x a" and "tendsto x b"
  shows "a = b"
  sorry

section \<open>Rudin 3.2 (c) -- Svaki konvergentan niz je ogranicen\<close>

(* mi22062_Nenad_Pesic_FORMULACIJA *)
lemma tendsto_bounded:
  fixes x :: "nat \<Rightarrow> 'a::metric_space"
  assumes "tendsto x a"
  shows "bounded x"
  sorry

end
