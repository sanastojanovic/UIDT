
(*<*)
theory MyTheory
    imports Main
begin
(*>*)

section \<open> Naslov \<close>

text \<open> Neki tekst. \<close>

lemma "rev (rev xs) = xs"
    by auto

theorem rev_cons: "rev (x # xs) = snoc (rev xs) x"
(*<*)oops(*>*)

text_raw \<open>\begin{exercise}[subtitle=Ovo je naslov zadatka]\<close>

text \<open> Sada sledi tekst zadatka \<close>

text_raw \<open> \begin{xca}{Definicija bla bla bla} Definisati funkciju: \<close>
consts snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list"

text_raw \<open>\end{xca}\<close>

text \<open> Ovde je kraj zadatka. \<close>

text_raw \<open> \end{exercise} \<close>

text \<open> \begin{thm}{(Teorema o nečemu)} Još jedan zadatak @{thm[mode=IfThen] le_trans} \end{thm}\<close>

paragraph \<open>Neki paragraf\<close>

text \<open> Neki tekst nakon paragrafa \<close>

subparagraph \<open>Podparagraf\<close>

txt \<open> Neki tekst nakon podparagrafa \<close>


lemma "le_trans x y"
    oops

(*<*)
end
(*>*)
