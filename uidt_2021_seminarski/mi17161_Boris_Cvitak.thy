theory mi17161_Boris_Cvitak
  imports Main
begin

text\<open>
  Link : https://www.imo-official.org/problems/IMO2019SL.pdf 
  Number theory : N1

  Find all pairs m, n of positive integers satisfying the equation
  (2^n - 1) * (2^n - 2) * (2^n - 4) * ... * (2^n - 2^(n-1)) = m!
\<close> 

primrec fact :: "nat \<Rightarrow> nat" where
"fact 0 = 1" |
"fact (Suc n) = (n+1) * (fact n)"


lemma
  fixes n m :: nat
  assumes "n > 0" "m > 0"
  shows "foldl (\<lambda> acc x. acc * (2^n - x)) 1 ([1..<n]::nat list) = (fact m)" 
  sorry

end