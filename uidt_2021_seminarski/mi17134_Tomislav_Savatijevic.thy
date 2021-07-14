theory mi17134_Tomislav_Savatijevic
  imports Complex_Main
begin
text\<open>

  Find the least positive integer n for which there exists a set {s1, s2,..., sn}
  consisting of n distrinct positive integers such that 
  (1 - 1/s1) * (1 - 1/s2) ... (1 - 1/sn) = 51/2010
  
\<close>

(*Seminarski 1*)


fun validan_skup :: "nat list \<Rightarrow> bool" where
  (*                                 da su svi pozitivni (x > 0)           da nema duplikata *)
  "validan_skup m \<longleftrightarrow> sorted m \<and> (length (filter (\<lambda> x. x = 0) m) = 0) \<and> (\<forall> x \<in> (set m). x \<notin> ((set m) - {x}))"

lemma
  fixes n::nat
  assumes "n > 0"
  shows "\<exists> m::nat list. length m = n \<and> 2010 * (foldl (\<lambda> acc x. acc * (1 - 1 / x)) 1  m) = 51 \<and> validan_skup m"
  sorry

