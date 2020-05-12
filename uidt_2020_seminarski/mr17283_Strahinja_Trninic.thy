theory mr17283_Strahinja_Trninic
  imports Main
begin

text \<open>
                      Isabelle projekat

Predmet: Uvod u interaktivno dokazivanje teorema
Profesor: prof. dr. Filip Maric
Asistent: prof. dr. Sana Stojanovic Djurdjevic

Student: Strahinja Trninic
Indeks: mr17283
Grupa: 4R

Zadatak: 
        51. Internacionalna Matematicka Olimpijada
                    Astana, Kazahstan, 2010.

            Lista problema sa resenjima
            -Kombinatorni zadatak: C3-

(https://www.imo-official.org/problems/IMO2010SL.pdf)
\<close>


text \<open>
Kratak opisa zadatka:

Data je sahovska tabla dimenzije 100\<times>100. Potrebno je pronaci broj razlicitih nacina
na koje mogu da se poredjaju 2500 kraljeva, pazeci na uslove:
pazeci na sledece uslove:
- Kraljevi ne semju da napadaju jedni druge
- Svaki red i svaka kolona mora da sadrzi tacno 25 kraljeva
- Cak iako se jedna konfiguracija moze dobiti od druge rotacijama ili simetrijama,
  one se idalje tretiraju kao dve razlicite konfiguracije.
\<close>


section \<open>Tabla\<close>

text \<open>Definisemo tablu za igranje.\<close>


text \<open>Prvo polje je dole-levo i ima koordinate (0, 0) a poslednje je gore-desno i ima koordinate (9, 9).\<close>

datatype broj = nula ("\<zero>") | jedan ("\<one>") | dva ("\<two>") | tri ("\<three>") | cetiri ("\<four>") | pet ("\<five>") | sest ("\<six>") | sedam ("\<seven>") | osam ("\<eight>") | devet ("\<nine>") (*| 
                deset ("\<one>\<zero>") | jedanaest ("\<one>\<one>") | dvanaest ("\<one>\<two>") | trinaest ("\<one>\<three>") | cetrnaest ("\<one>\<four>") | petnaest ("\<one>\<five>") | sesnaest ("\<one>\<six>") | sedamnaest ("\<one>\<seven>") | osamnaest ("\<one>\<eight>") | deventaest ("\<one>\<nine>") |
                ddeset ("\<two>\<zero>") | djedan ("\<two>\<one>") | ddva ("\<two>\<two>") | dtri ("\<two>\<three>") | dcetiri ("\<two>\<four>") | dpet ("\<two>\<five>") | dsest ("\<two>\<six>") | dsedam ("\<two>\<seven>") | dosam ("\<two>\<eight>") | ddevet ("\<two>\<nine>") |
                tdeset ("\<three>\<zero>") | tjedan ("\<three>\<one>") | tdva ("\<three>\<two>") | ttri ("\<three>\<three>") | tcetiri ("\<three>\<four>") | tpet ("\<three>\<five>") | tsest ("\<three>\<six>") | tsedam ("\<three>\<seven>") | tosam ("\<three>\<eight>") | tdevet ("\<three>\<nine>") |
                cdeset ("\<four>\<zero>") | cjedan ("\<four>\<one>") | cdva ("\<four>\<two>") | ctri ("\<four>\<three>") | ccetiri ("\<four>\<four>") | cpet ("\<four>\<five>") | csest ("\<four>\<six>") | csedam ("\<four>\<seven>") | cosam ("\<four>\<eight>") | cdevet ("\<four>\<nine>") |
                pdeset ("\<five>\<zero>") | pjedan ("\<five>\<one>") | pdva ("\<five>\<two>") | ptri ("\<five>\<three>") | pcetiri ("\<five>\<four>") | ppet ("\<five>\<five>") | psest ("\<five>\<six>") | psedam ("\<five>\<seven>") | posam ("\<five>\<eight>") | pdevet ("\<five>\<nine>") |
                sdeset ("\<six>\<zero>") | sjedan ("\<six>\<one>") | sdva ("\<six>\<two>") | stri ("\<six>\<three>") | scetiri ("\<six>\<four>") | spet ("\<six>\<five>") | ssest ("\<six>\<six>") | ssedam ("\<six>\<seven>") | sosam ("\<six>\<eight>") | sdevet ("\<six>\<nine>") |
                sedeset ("\<seven>\<zero>") | sejedan ("\<seven>\<one>") | sedva ("\<seven>\<two>") | setri ("\<seven>\<three>") | secetiri ("\<seven>\<four>") | sepet ("\<seven>\<five>") | sesest ("7\<six>") | sesedam ("\<seven>\<seven>") | seosam ("\<seven>\<eight>") | sedevet ("\<seven>\<nine>") |
                odeset ("\<eight>\<zero>") | ojedan ("\<eight>\<one>") | odva ("\<eight>\<two>") | otri ("\<eight>\<three>") | ocetiri ("\<eight>\<four>") | opet ("\<eight>\<five>") | osest ("\<eight>\<six>") | osedam ("\<eight>\<seven>") | oosam ("\<eight>\<eight>") | odevet ("\<eight>\<nine>") |
                dedeset ("\<nine>\<zero>") | dejedan ("\<nine>\<one>") | dedva ("\<nine>\<two>") | detri ("\<nine>\<three>") | decetiri ("\<nine>\<four>") | depet ("\<nine>\<five>") | desest ("\<nine>\<six>") | desedam ("\<nine>\<seven>") | deosam ("\<nine>\<eight>") | dedevet ("\<nine>\<nine>")*)

type_synonym polje = "broj \<times> broj"


section \<open>Igra\<close>

text \<open>Definisemo locale u kome cemo definisati sve uslove. Nitpick bi onda trebalo da pronadje barem jednu
      trazenu konfiguraciju.\<close>

locale Igra = 
  (*Posto koristimo diskretan podskup prirodnih brojeva, moramo izpocetka da definisemo funkcije poput sledbenika, razlike brojeva, ...
    koje ce nam kasnije trebati za odredjivanje susednih polja zadatog polja.*)
  fixes sledbenik :: "broj \<Rightarrow> broj"
  assumes sledbenik_Eksplicitno: "sledbenik x = (if x = \<zero> then \<one> else if x = \<one> then \<two> else if x = \<two> then \<three> else if x = \<three> then \<four> else if x = \<four> then \<five> else if x = \<five> then \<six> else if x = \<six> then \<seven> else if x = \<seven> then \<eight> else \<nine>)"
  (*
  else if x = \<one>\<zero> then \<one>\<one> else if x = \<one>\<two> then ...
  *)

  fixes m0nus1 :: "broj \<Rightarrow> broj"
  assumes m0nus1_Eksplicitno: "m0nus1 x = (if x = \<nine> then \<eight> else if x = \<eight> then \<seven> else if x = \<seven> then \<six> else if x = \<six> then \<five> else if x = \<five> then \<four> else if x = \<four> then \<three> else if x = \<three> then \<two> else if x = \<two> then \<one> else \<zero>)"

  (*Definisemo poredak brojeva:*)
  fixes manje :: "broj \<Rightarrow> broj \<Rightarrow> bool" (infixl "\<prec>" 100)
  assumes manje_IRefl: "\<And>x.(\<not>(x \<prec> x))"
  assumes manje_Trans: "\<And>x y z.(x \<prec> y \<and> y \<prec> z \<longrightarrow> x \<prec> z)"
  assumes manje_Sledbenik: "\<And>x.((x \<noteq> \<nine>)\<longrightarrow> x \<prec> (sledbenik x))"
  assumes manje_Najmanje: "\<And>x.((x \<noteq> \<zero>) \<longrightarrow> \<zero> \<prec> x)" (*Nepotrebno, ali pomaze!*)
  assumes manje_Najvece: "\<And>x.((x \<noteq> \<nine>) \<longrightarrow> x \<prec> \<nine>)" (*Nepotrebno, ali pomaze!*)

  (*Definisemo unarnu relaciju "Kralj je na polju xy"*)
  fixes kralj :: "broj \<Rightarrow> broj \<Rightarrow> bool"

  assumes vrsta_Tacno25: "\<And>x.\<exists>y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25.
                  (kralj x y1 \<and> kralj x y2 \<and> kralj x y3 \<and> kralj x y4 \<and> kralj x y5 \<and> kralj x y6 \<and> kralj x y7 \<and> kralj x y8 \<and> kralj x y8 \<and> kralj x y9 \<and> kralj x y10 \<and> kralj x y11 \<and> kralj x y12 \<and> kralj x y13 \<and> kralj x y14 \<and> kralj x y15 \<and> kralj x y16 \<and> kralj x y17 \<and> kralj x y18 \<and> kralj x y19 \<and> kralj x y20 \<and> kralj x y21 \<and> kralj x y22 \<and> kralj x y23 \<and> kralj x y24 \<and> kralj x y25
                   \<and> (\<forall>t.(t \<notin> {y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19, y20, y21, y22, y23, y24, y25} \<longrightarrow> \<not>kralj x t)))"

  assumes kolona_Tacno25: "\<And>y.\<exists>x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25.
                  (kralj x1 y \<and> kralj x2 y \<and> kralj x3 y \<and> kralj x4 y \<and> kralj x5 y \<and> kralj x6 y \<and> kralj x7 y \<and> kralj x8 y \<and> kralj x8 y \<and> kralj x9 y \<and> kralj x10 y \<and> kralj x11 y \<and> kralj x12 y \<and> kralj x13 y \<and> kralj x14 y \<and> kralj x15 y \<and> kralj x16 y \<and> kralj x17 y \<and> kralj x18 y \<and> kralj x19 y \<and> kralj x20 y \<and> kralj x21 y \<and> kralj x22 y \<and> kralj x23 y \<and> kralj x24 y \<and> kralj x25 y
                   \<and> (\<forall>t.(t \<notin> {x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25} \<longrightarrow> \<not>kralj t y)))"

(*Mora da postoji bolji nacin od ovoga:
  assumes kralj_Tacno2500: "\<exists>x1 y1 x2 y2 ... x2500 y2500
                         (kralj x1 y1 \<and> ... \<and> kralj x2500 y2500 \<and>
                          (x1 \<noteq> x2 \<or> y1 \<noteq> y2) \<and> (x1 \<noteq> x3 \<or> y1 \<noteq> y3) \<and> ... \<and> (x1 \<noteq> x2500 \<or> y1 \<noteq> y2500) \<and>
                          .
                          .
                          .
                          (x2498 \<noteq> x2499 \<or> y2498 \<noteq> y2499) \<and> (x2498 \<noteq> x2500 \<or> y2498 \<noteq> y2500) \<and>
                          (x2499 \<noteq> x2500 \<or> y2499 \<noteq> y2500))" *)
begin
text \<open>Neke provere\<close>

(*Pitamo se da li je nas model kontradiktoran.*)
lemma "False"
  oops (*Sledgehammer ne uspeva da pronadje kontradikciju!*)

lemma "\<two> \<prec> \<eight>"
  by (metis (full_types) broj.distinct(11) broj.distinct(13) broj.distinct(19) broj.distinct(21) broj.distinct(23) broj.distinct(25) broj.distinct(27) broj.distinct(29) broj.distinct(3) broj.distinct(35) broj.distinct(37) broj.distinct(39) broj.distinct(41) broj.distinct(43) broj.distinct(47) broj.distinct(49) broj.distinct(5) broj.distinct(51) broj.distinct(53) broj.distinct(55) broj.distinct(59) broj.distinct(61) broj.distinct(63) broj.distinct(65)  broj.distinct(69) broj.distinct(7) broj.distinct(71) broj.distinct(73) broj.distinct(77) broj.distinct(79) broj.distinct(83) broj.distinct(87) broj.distinct(9) manje_Sledbenik manje_Trans sledbenik_Eksplicitno)

end

section \<open>Nitpick\<close>


end