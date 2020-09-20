theory mi16166_Trtica_Mateja
  imports Complex_Main
begin

text \<open>
Zadatak 1, treci razred.
Link: https://imomath.com/srb/zadaci/2014_okruzno.pdf
Tekst zadatka:
Neka su x,y,z realni brojevi takvi da vazi x+y+z=0. Dokazati da vazi nejednakost:

  6*(x^3 + y^3 + z^3)\<le> (x^2 + y^2 + z^2)^3
\<close>
lemma kub_binoma:
  fixes x y :: real
  assumes "x\<ge>0" "y\<ge>0"
  shows  "(x-y)^3 =x^3-3*(x^2)*y + 3*x*(y^2)- y^3" 
proof-
have "(x-y)^3 = (x-y)*(x-y)*(x-y)" 
  by (simp add: power3_eq_cube)
  also have "... = (x*x-x*y-y*x+y*y)*(x-y)"
    by (simp add: add.commute add_diff_eq mult.commute right_diff_distrib')
   also have "... =x*x*x - x*x*y - x*y*x + x*y*y  - y*x*x + y*x*y + y*y*x - y*y*y" sledgehammer
      using assms by blast
  finally show ?thesis
qed





lemma p1:
  fixes x y z :: real
  assumes "x \<ge>0" "y \<ge>0" "z =-x -y"
  shows  "(x^3 + y^3 + z^3)^2 = 9*(x^2)*(y^2)*(x+y)^2"
  using assms
proof-
  have "(x^3 + y^3 + z^3)^2 = (x^3 + y^3 + (-x-y)^3)^2 " using assms(3) by auto
  have "(x^3 + y^3 + z^3)^2 =(-3*(-(x^2))*y - 3*(-x)*(y^2))^2" by auto
    then show ?thesis
qed


  
lemma zadatak:
  fixes x y z :: real
  assumes "x + y + z = 0"
  shows "6*(x^3 + y^3 + z^3)\<le> (x^2 + y^2 + z^2)^3"
  
  
end