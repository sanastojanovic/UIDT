theory mi16096_Milena_Stojic_Binommial_coefficients
  imports Complex_Main

begin
text
\<open>
  Teorija u kojoj definišemo binomni koeficijent i posle dokazujemo
  sve važne identitete sa njima.
\<close>

text
\<open>
  Pre nego što definišemo pojam binomnog koeficijenta, neophodan
  nam je pojam faktorijela (proizvoda uzastopnih prirodnih brojeva)
\<close>
primrec fact :: "nat \<Rightarrow> nat" where
"fact 0 = 1" |
"fact (Suc n) = (Suc n) * (fact n)"


value "fact 5"

text
\<open>
  Iako ih nećemo koristiti u ovom fajlu, ovde ćemo definisati
  i proizvod uzastopnih parnih ili uzastopnih neparnih brojeva.
  (proizvod prvih n neparnih brojeva)
\<close>
primrec fact2 :: "nat \<Rightarrow> nat" where
"fact2 0 = 1" |
"fact2 (Suc n) = (2 * (Suc n) - 1) * (fact2 n)"

value "fact2 3"

text
\<open>
  Sada definišemo binomni koeficijent.
\<close>
definition binomm_core :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"binomm_core n k = ((fact n) div (fact k)) div (fact (n - k))"

definition binomm :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"binomm n k =  (if n \<ge> k then (binomm_core n k) else 0)" \<comment> \<open>Ne dozvoljavamo nekorektne argumente.\<close>

value "binomm 5 5"
value "binomm 5 0"
value "binomm 5 2" 
value "binomm 5 3" \<comment> \<open>Na ovom primeru vidimo da je (n k) i (n n-k) jednako. I to je identitet koji ćemo dokazivati.\<close>
end