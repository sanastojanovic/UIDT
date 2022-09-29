theory mi18096_Jelena_Cankovic
  imports Complex_Main 
begin

text\<open>
Find all functions f: R+ \<rightarrow> R+ such that f(x + f(y))= f(x + y) + f(y)
for all x, y \<in> R+.

https://www.imo-official.org/problems/IMO2007SL.pdf
A4
\<close>


lemma final:
  fixes x y::real
  assumes "x > 0" "y > 0" "\<forall>x. \<forall>y. f(x + f(y)) = f(x + y) + f(y)" "\<forall>x. f x > 0"
  shows "f x = 2*x"
  sorry


lemma help1:
  fixes f :: "real \<Rightarrow> real"
  assumes "\<forall>x y. x > 0 \<and> y > 0 \<longrightarrow> f(x + f y) = f(x + y) + f y""\<forall> x. f x > 0"
  shows"\<forall>y. y > 0 \<longrightarrow>  f y > y"
  sorry

lemma help2:
  fixes f g:: "real \<Rightarrow> real"
  assumes "\<forall>x::real. \<forall>y. x > 0 \<and> y > 0 \<longrightarrow> f(x + f(y)) = f(x + y) + f(y)""\<forall>x. f x > 0"
        "\<forall> x. x > 0 \<longrightarrow> g x = f x - x"
      shows"\<forall>t y. t > y \<longrightarrow> g(t + g(y)) = g(t) + y"
  sorry

lemma help3:
  fixes f g:: "real \<Rightarrow> real"
  assumes "\<forall>x::real. \<forall>y. x > 0 \<and> y > 0 \<longrightarrow> f(x + f(y)) = f(x + y) + f(y)""\<forall>x. f x > 0"
        "\<forall> x. x > 0 \<longrightarrow> g x = f x - x"
      shows"inj g"
  sorry

lemma help4:
  fixes f g:: "real \<Rightarrow> real"
  assumes  "\<forall>x::real. \<forall>y. x > 0 \<and> y > 0 \<longrightarrow> f(x + f(y)) = f(x + y) + f(y)""\<forall>x. f x > 0"
        "\<forall> x. x > 0 \<longrightarrow> g x = f x - x"
      shows "\<forall> u v. g(u) + g(v) = g(u+v)"
  sorry
  

lemma help5:
  fixes f g :: "real \<Rightarrow> real"
  assumes "\<forall>x::real. \<forall>y. x > 0 \<and> y > 0 \<longrightarrow> f(x + f(y)) = f(x + y) + f(y)""\<forall>x. f x > 0"
        "\<forall> x. g x = f x - x"
      shows "\<forall> x. x > 0 \<longrightarrow> g(x) = x"
  sorry
  


end