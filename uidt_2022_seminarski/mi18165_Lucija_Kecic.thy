theory mi18165_Lucija_Kecic
  imports Main Complex_Main

begin

(*Let a, b and c be positive real numbers
satisfying min(a+b, b+c, c+a) > \<surd>2 and
a^2+b^2+c^2=3
Prove that
a/(b+c-a)^2 + b/(c+a-b)^2+c(a+b-c)^2\<ge>3/(a*b*c)^2
*)

fun min :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "min a b c = 
    (if a>b | c>b then b
    else if a>c | b>c then c
    else a)"

lemma problem:
  fixes a b c :: "real"
  assumes "a>0" "b>0" "c>0"
  assumes "min(a+b)(b+c)(c+a) > sqrt 2"
  assumes "a^2 + b^2 + c^2 = 3"
  shows "a/(b+c-a)^2 + b/(c+a-b)^2 + c/(a+b-c)^2 \<ge> 3/(a*b*c)^2"
  using assms
  oops


end