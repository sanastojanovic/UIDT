theory mr17283_Strahinja_Trninic
  imports Main "HOL-Proofs-Extraction.Util" "HOL-Library.Realizers" "HOL-Library.Code_Target_Numeral"
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


text \<open>Prvo polje je gore-levo i ima koordinate (0, 0) a poslednje je dole-desno i ima koordinate (11, 11).\<close>

datatype broj = nula ("\<zero>") | jedan ("\<one>") | dva ("\<two>") | tri ("\<three>") | cetiri ("\<four>") | pet ("\<five>") | sest ("\<six>") (*| sedam ("\<seven>") | osam ("\<eight>") | devet ("\<nine>") | 
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
(*  fixes sledbenik :: "broj \<Rightarrow> broj"
  assumes sledbenik_Eksplicitno: "sledbenik x = (if x = \<zero> then \<one> else if x = \<one> then \<two> else if x = \<two> then \<three> else if x = \<three> then \<four> else if x = \<four> then \<five> else if x = \<five> then \<six> else if x = \<six> then \<seven> else if x = \<seven> then \<eight> else if x = \<nine> then \<one>\<zero> else \<one>\<one>)"
  (*...*)

  fixes m0nus1 :: "broj \<Rightarrow> broj"
  assumes m0nus1_Eksplicitno: "m0nus1 x = (if x = \<one>\<one> then \<one>\<zero> else if x = \<one>\<zero> then \<nine> else if x = \<nine> then \<eight> else if x = \<eight> then \<seven> else if x = \<seven> then \<six> else if x = \<six> then \<five> else if x = \<five> then \<four> else if x = \<four> then \<three> else if x = \<three> then \<two> else if x = \<two> then \<one> else \<zero>)"
  (*...*)

  (*Definisemo poredak brojeva:*)
  fixes manje :: "broj \<Rightarrow> broj \<Rightarrow> bool" (infixl "\<prec>" 100)
  assumes manje_IRefl: "\<And>x.(\<not>(x \<prec> x))"
  assumes manje_Trans: "\<And>x y z.(x \<prec> y \<and> y \<prec> z \<longrightarrow> x \<prec> z)"
  assumes manje_Sledbenik: "\<And>x.((x \<noteq> \<one>\<one>)\<longrightarrow> x \<prec> (sledbenik x))"
  assumes manje_Najmanje: "\<And>x.((x \<noteq> \<zero>) \<longrightarrow> \<zero> \<prec> x)" (*Nepotrebno, ali pomaze!*)
  assumes manje_Najvece: "\<And>x.((x \<noteq> \<one>\<one>) \<longrightarrow> x \<prec> \<one>\<one>)" (*Nepotrebno, ali pomaze!*)

*)

  (*Definisemo unarnu relaciju "Kralj je na polju (x, y)"*)
  fixes kralj :: "broj \<Rightarrow> broj \<Rightarrow> bool"

  (*assumes vrsta_Tacno25: "\<And>x.\<exists>y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25.
                  (kralj x y1 \<and> kralj x y2 \<and> kralj x y3 \<and> kralj x y4 \<and> kralj x y5 \<and> kralj x y6 \<and> kralj x y7 \<and> kralj x y8 \<and> kralj x y8 \<and> kralj x y9 \<and> kralj x y10 \<and> kralj x y11 \<and> kralj x y12 \<and> kralj x y13 \<and> kralj x y14 \<and> kralj x y15 \<and> kralj x y16 \<and> kralj x y17 \<and> kralj x y18 \<and> kralj x y19 \<and> kralj x y20 \<and> kralj x y21 \<and> kralj x y22 \<and> kralj x y23 \<and> kralj x y24 \<and> kralj x y25
                   \<and> (\<And>t.(t \<notin> {y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19, y20, y21, y22, y23, y24, y25} \<longrightarrow> \<not>kralj x t)))"

  assumes kolona_Tacno25: "\<And>y.\<exists>x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25.
                  (kralj x1 y \<and> kralj x2 y \<and> kralj x3 y \<and> kralj x4 y \<and> kralj x5 y \<and> kralj x6 y \<and> kralj x7 y \<and> kralj x8 y \<and> kralj x8 y \<and> kralj x9 y \<and> kralj x10 y \<and> kralj x11 y \<and> kralj x12 y \<and> kralj x13 y \<and> kralj x14 y \<and> kralj x15 y \<and> kralj x16 y \<and> kralj x17 y \<and> kralj x18 y \<and> kralj x19 y \<and> kralj x20 y \<and> kralj x21 y \<and> kralj x22 y \<and> kralj x23 y \<and> kralj x24 y \<and> kralj x25 y
                   \<and> (\<And>t.(t \<notin> {x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25} \<longrightarrow> \<not>kralj t y)))" *)
  assumes vrsta_Tacno4: "\<forall>x.\<exists>y1 y2 y3 y4.(kralj x y1 \<and> kralj x y2 \<and> kralj x y3 \<and> kralj x y4 \<and>
                         y1 \<noteq> y2 \<and> y1 \<noteq> y3 \<and> y1 \<noteq> y4 \<and>
                         y2 \<noteq> y3 \<and> y2 \<noteq> y4 \<and>
                         y3 \<noteq> y4 \<and>
                         (\<forall>t.(t \<notin> {y1, y2, y3, y4} \<longrightarrow> \<not>kralj x t)))"
  assumes kolona_Tacno4: "\<forall>y.\<exists>x1 x2 x3 x4.(kralj x1 y \<and> kralj x2 y \<and> kralj x3 y \<and> kralj x4 y \<and>
                          x1 \<noteq> x2 \<and> x1 \<noteq> x3 \<and> x1 \<noteq> x4 \<and>
                          x2 \<noteq> x3 \<and> x2 \<noteq> x4 \<and>
                          x3 \<noteq> x4 \<and>  
                          (\<forall>t.(t \<notin> {x1, x2, x3, x4} \<longrightarrow> \<not>kralj t y)))"
 (*assumes kralj_Tacno4: "\<exists>x1 y1 x2 y2 x3 y3 x4 y4.(kralj x1 y1 \<and> kralj x2 y2 \<and> kralj x3 y3 \<and> kralj x4 y4)"*)

assumes kralj_Const: "(kralj \<zero> \<zero> \<longrightarrow> (\<not>kralj \<zero> \<one> \<and> \<not>kralj \<one> \<zero> \<and> \<not>kralj \<one> \<one>)) \<and>
                      (kralj \<zero> \<one> \<longrightarrow> (\<not>kralj \<zero> \<zero> \<and> \<not>kralj \<zero> \<two> \<and> \<not>kralj \<one> \<zero> \<and> \<not>kralj \<one> \<one> \<and> \<not>kralj \<one> \<two>)) \<and>
                      (kralj \<zero> \<two> \<longrightarrow> (\<not>kralj \<zero> \<one> \<and> \<not>kralj \<zero> \<three> \<and> \<not>kralj \<one> \<one> \<and> \<not>kralj \<one> \<two> \<and> \<not>kralj \<one> \<three>)) \<and>
                      (kralj \<zero> \<three> \<longrightarrow> (\<not>kralj \<zero> \<two> \<and> \<not>kralj \<zero> \<four> \<and> \<not>kralj \<one> \<two> \<and> \<not>kralj \<one> \<three> \<and> \<not>kralj \<one> \<four>)) \<and>
                      (kralj \<zero> \<four> \<longrightarrow> (\<not>kralj \<zero> \<three> \<and> \<not>kralj \<zero> \<five> \<and> \<not>kralj \<one> \<three> \<and> \<not>kralj \<one> \<four> \<and> \<not>kralj \<one> \<five>)) \<and>
                      (kralj \<zero> \<five> \<longrightarrow> (\<not>kralj \<zero> \<four> \<and> \<not>kralj \<zero> \<six> \<and> \<not>kralj \<one> \<four> \<and> \<not>kralj \<one> \<five> \<and> \<not>kralj \<one> \<six>)) \<and>
                      (kralj \<zero> \<six> \<longrightarrow> (\<not>kralj \<zero> \<five> \<and> \<not>kralj \<one> \<five> \<and> \<not>kralj \<one> \<six>)) \<and>

                      (kralj \<one> \<zero> \<longrightarrow> (\<not>kralj \<one> \<one> \<and> \<not>kralj \<zero> \<zero> \<and> \<not>kralj \<zero> \<one> \<and> \<not>kralj \<two> \<zero> \<and> \<not>kralj \<two> \<one>)) \<and>
                      (kralj \<one> \<one> \<longrightarrow> (\<not>kralj \<one> \<zero> \<and> \<not>kralj \<one> \<two> \<and> \<not>kralj \<zero> \<zero> \<and> \<not>kralj \<zero> \<one> \<and> \<not>kralj \<zero> \<two> \<and> \<not>kralj \<two> \<zero> \<and> \<not>kralj \<two> \<one> \<and> \<not>kralj \<two> \<two>)) \<and>
                      (kralj \<one> \<two> \<longrightarrow> (\<not>kralj \<one> \<one> \<and> \<not>kralj \<one> \<three> \<and> \<not>kralj \<zero> \<one> \<and> \<not>kralj \<zero> \<two> \<and> \<not>kralj \<zero> \<three> \<and> \<not>kralj \<two> \<one> \<and> \<not>kralj \<two> \<two> \<and> \<not>kralj \<two> \<three>)) \<and>
                      (kralj \<one> \<three> \<longrightarrow> (\<not>kralj \<one> \<two> \<and> \<not>kralj \<one> \<four> \<and> \<not>kralj \<zero> \<two> \<and> \<not>kralj \<zero> \<three> \<and> \<not>kralj \<zero> \<four> \<and> \<not>kralj \<two> \<two> \<and> \<not>kralj \<two> \<three> \<and> \<not>kralj \<two> \<four>)) \<and>
                      (kralj \<one> \<four> \<longrightarrow> (\<not>kralj \<one> \<three> \<and> \<not>kralj \<one> \<five> \<and> \<not>kralj \<zero> \<three> \<and> \<not>kralj \<zero> \<four> \<and> \<not>kralj \<zero> \<five> \<and> \<not>kralj \<two> \<three> \<and> \<not>kralj \<two> \<four> \<and> \<not>kralj \<two> \<five>)) \<and>
                      (kralj \<one> \<five> \<longrightarrow> (\<not>kralj \<one> \<four> \<and> \<not>kralj \<one> \<six> \<and> \<not>kralj \<zero> \<four> \<and> \<not>kralj \<zero> \<five> \<and> \<not>kralj \<zero> \<six> \<and> \<not>kralj \<two> \<four> \<and> \<not>kralj \<two> \<five> \<and> \<not>kralj \<two> \<six>)) \<and>
                      (kralj \<one> \<six> \<longrightarrow> (\<not>kralj \<one> \<five> \<and> \<not>kralj \<zero> \<five> \<and> \<not>kralj \<zero> \<six> \<and> \<not>kralj \<two> \<five> \<and> \<not>kralj \<two> \<six>)) \<and>

                      (kralj \<two> \<zero> \<longrightarrow> (\<not>kralj \<two> \<one> \<and> \<not>kralj \<one> \<zero> \<and> \<not>kralj \<one> \<one> \<and> \<not>kralj \<three> \<zero> \<and> \<not>kralj \<three> \<one>)) \<and>
                      (kralj \<two> \<one> \<longrightarrow> (\<not>kralj \<two> \<zero> \<and> \<not>kralj \<two> \<two> \<and> \<not>kralj \<one> \<zero> \<and> \<not>kralj \<one> \<one> \<and> \<not>kralj \<one> \<two> \<and> \<not>kralj \<three> \<zero> \<and> \<not>kralj \<three> \<one> \<and> \<not>kralj \<three> \<two>)) \<and>
                      (kralj \<two> \<two> \<longrightarrow> (\<not>kralj \<two> \<one> \<and> \<not>kralj \<two> \<three> \<and> \<not>kralj \<one> \<one> \<and> \<not>kralj \<one> \<two> \<and> \<not>kralj \<one> \<three> \<and> \<not>kralj \<three> \<one> \<and> \<not>kralj \<three> \<two> \<and> \<not>kralj \<three> \<three>)) \<and>
                      (kralj \<two> \<three> \<longrightarrow> (\<not>kralj \<two> \<two> \<and> \<not>kralj \<two> \<four> \<and> \<not>kralj \<one> \<two> \<and> \<not>kralj \<one> \<three> \<and> \<not>kralj \<one> \<four> \<and> \<not>kralj \<three> \<two> \<and> \<not>kralj \<three> \<three> \<and> \<not>kralj \<three> \<four>)) \<and>
                      (kralj \<two> \<four> \<longrightarrow> (\<not>kralj \<two> \<three> \<and> \<not>kralj \<two> \<five> \<and> \<not>kralj \<one> \<three> \<and> \<not>kralj \<one> \<four> \<and> \<not>kralj \<one> \<five> \<and> \<not>kralj \<three> \<three> \<and> \<not>kralj \<three> \<four> \<and> \<not>kralj \<three> \<five>)) \<and>
                      (kralj \<two> \<five> \<longrightarrow> (\<not>kralj \<two> \<four> \<and> \<not>kralj \<two> \<six> \<and> \<not>kralj \<one> \<four> \<and> \<not>kralj \<one> \<five> \<and> \<not>kralj \<one> \<six> \<and> \<not>kralj \<three> \<four> \<and> \<not>kralj \<three> \<five> \<and> \<not>kralj \<three> \<six>)) \<and>
                      (kralj \<two> \<six> \<longrightarrow> (\<not>kralj \<two> \<five> \<and> \<not>kralj \<one> \<five> \<and> \<not>kralj \<one> \<six> \<and> \<not>kralj \<three> \<five> \<and> \<not>kralj \<three> \<six>)) \<and>

                      (kralj \<three> \<zero> \<longrightarrow> (\<not>kralj \<three> \<one> \<and> \<not>kralj \<two> \<zero> \<and> \<not>kralj \<two> \<one> \<and> \<not>kralj \<four> \<zero> \<and> \<not>kralj \<four> \<one>)) \<and>
                      (kralj \<three> \<one> \<longrightarrow> (\<not>kralj \<three> \<zero> \<and> \<not>kralj \<three> \<two> \<and> \<not>kralj \<two> \<zero> \<and> \<not>kralj \<two> \<one> \<and> \<not>kralj \<two> \<two> \<and> \<not>kralj \<four> \<zero> \<and> \<not>kralj \<four> \<one> \<and> \<not>kralj \<four> \<two>)) \<and>
                      (kralj \<three> \<two> \<longrightarrow> (\<not>kralj \<three> \<one> \<and> \<not>kralj \<three> \<three> \<and> \<not>kralj \<two> \<one> \<and> \<not>kralj \<two> \<two> \<and> \<not>kralj \<two> \<three> \<and> \<not>kralj \<four> \<one> \<and> \<not>kralj \<four> \<two> \<and> \<not>kralj \<four> \<three>)) \<and>
                      (kralj \<three> \<three> \<longrightarrow> (\<not>kralj \<three> \<two> \<and> \<not>kralj \<three> \<four> \<and> \<not>kralj \<two> \<two> \<and> \<not>kralj \<two> \<three> \<and> \<not>kralj \<two> \<four> \<and> \<not>kralj \<four> \<two> \<and> \<not>kralj \<four> \<three> \<and> \<not>kralj \<four> \<four>)) \<and>
                      (kralj \<three> \<four> \<longrightarrow> (\<not>kralj \<three> \<three> \<and> \<not>kralj \<three> \<five> \<and> \<not>kralj \<two> \<three> \<and> \<not>kralj \<two> \<four> \<and> \<not>kralj \<two> \<five> \<and> \<not>kralj \<four> \<three> \<and> \<not>kralj \<four> \<four> \<and> \<not>kralj \<four> \<five>)) \<and>
                      (kralj \<three> \<five> \<longrightarrow> (\<not>kralj \<three> \<four> \<and> \<not>kralj \<three> \<six> \<and> \<not>kralj \<two> \<four> \<and> \<not>kralj \<two> \<five> \<and> \<not>kralj \<two> \<six> \<and> \<not>kralj \<four> \<four> \<and> \<not>kralj \<four> \<five> \<and> \<not>kralj \<four> \<six>)) \<and>
                      (kralj \<three> \<six> \<longrightarrow> (\<not>kralj \<three> \<five> \<and> \<not>kralj \<two> \<five> \<and> \<not>kralj \<two> \<six> \<and> \<not>kralj \<four> \<five> \<and> \<not>kralj \<four> \<six>)) \<and>

                      (kralj \<four> \<zero> \<longrightarrow> (\<not>kralj \<four> \<one> \<and> \<not>kralj \<three> \<zero> \<and> \<not>kralj \<three> \<one> \<and> \<not>kralj \<five> \<zero> \<and> \<not>kralj \<five> \<one>)) \<and>
                      (kralj \<four> \<one> \<longrightarrow> (\<not>kralj \<four> \<zero> \<and> \<not>kralj \<four> \<two> \<and> \<not>kralj \<three> \<zero> \<and> \<not>kralj \<three> \<one> \<and> \<not>kralj \<three> \<two> \<and> \<not>kralj \<five> \<zero> \<and> \<not>kralj STRAX \<one> \<and> \<not>kralj \<five> \<two>)) \<and>
                      (kralj \<four> \<two> \<longrightarrow> (\<not>kralj \<four> \<one> \<and> \<not>kralj \<four> \<three> \<and> \<not>kralj \<three> \<one> \<and> \<not>kralj \<three> \<two> \<and> \<not>kralj \<three> \<three> \<and> \<not>kralj \<five> \<one> \<and> \<not>kralj \<five> \<two> \<and> \<not>kralj \<five> \<three>)) \<and>
                      (kralj \<four> \<three> \<longrightarrow> (\<not>kralj \<four> \<two> \<and> \<not>kralj \<four> \<four> \<and> \<not>kralj \<three> \<two> \<and> \<not>kralj \<three> \<three> \<and> \<not>kralj \<three> \<four> \<and> \<not>kralj \<five> \<two> \<and> \<not>kralj \<five> \<three> \<and> \<not>kralj \<five> \<four>)) \<and>
                      (kralj \<four> \<four> \<longrightarrow> (\<not>kralj \<four> \<three> \<and> \<not>kralj \<four> \<five> \<and> \<not>kralj \<three> \<three> \<and> \<not>kralj \<three> \<four> \<and> \<not>kralj \<three> \<five> \<and> \<not>kralj \<five> \<three> \<and> \<not>kralj \<five> \<four> \<and> \<not>kralj \<five> \<five>)) \<and>
                      (kralj \<four> \<five> \<longrightarrow> (\<not>kralj \<four> \<four> \<and> \<not>kralj \<four> \<six> \<and> \<not>kralj \<three> \<four> \<and> \<not>kralj \<three> \<five> \<and> \<not>kralj \<three> \<six> \<and> \<not>kralj \<five> \<four> \<and> \<not>kralj \<five> \<five> \<and> \<not>kralj \<five> \<six>)) \<and>
                      (kralj \<four> \<six> \<longrightarrow> (\<not>kralj \<four> \<five> \<and> \<not>kralj \<three> \<five> \<and> \<not>kralj \<three> \<six> \<and> \<not>kralj \<five> \<five> \<and> \<not>kralj \<five> \<six>)) \<and>

                      (kralj \<five> \<zero> \<longrightarrow> (\<not>kralj \<five> \<one> \<and> \<not>kralj \<four> \<zero> \<and> \<not>kralj \<four> \<one> \<and> \<not>kralj \<six> \<zero> \<and> \<not>kralj \<six> \<one>)) \<and>
                      (kralj \<five> \<one> \<longrightarrow> (\<not>kralj \<five> \<zero> \<and> \<not>kralj \<five> \<two> \<and> \<not>kralj \<four> \<zero> \<and> \<not>kralj \<four> \<one> \<and> \<not>kralj \<four> \<two> \<and> \<not>kralj \<six> \<zero> \<and> \<not>kralj \<six> \<one> \<and> \<not>kralj \<six> \<two>)) \<and>
                      (kralj \<five> \<two> \<longrightarrow> (\<not>kralj \<five> \<one> \<and> \<not>kralj \<five> \<three> \<and> \<not>kralj \<four> \<one> \<and> \<not>kralj \<four> \<two> \<and> \<not>kralj \<four> \<three> \<and> \<not>kralj \<six> \<one> \<and> \<not>kralj \<six> \<two> \<and> \<not>kralj \<six> \<three>)) \<and>
                      (kralj \<five> \<three> \<longrightarrow> (\<not>kralj \<five> \<two> \<and> \<not>kralj \<five> \<four> \<and> \<not>kralj \<four> \<two> \<and> \<not>kralj \<four> \<three> \<and> \<not>kralj \<four> \<four> \<and> \<not>kralj \<six> \<two> \<and> \<not>kralj \<six> \<three> \<and> \<not>kralj \<six> \<four>)) \<and>
                      (kralj \<five> \<four> \<longrightarrow> (\<not>kralj \<five> \<three> \<and> \<not>kralj \<five> \<five> \<and> \<not>kralj \<four> \<three> \<and> \<not>kralj \<four> \<four> \<and> \<not>kralj \<four> \<five> \<and> \<not>kralj \<six> \<three> \<and> \<not>kralj \<six> \<four> \<and> \<not>kralj \<six> \<five>)) \<and>
                      (kralj \<five> \<five> \<longrightarrow> (\<not>kralj \<five> \<four> \<and> \<not>kralj \<five> \<six> \<and> \<not>kralj \<four> \<four> \<and> \<not>kralj \<four> \<five> \<and> \<not>kralj \<four> \<six> \<and> \<not>kralj \<six> \<four> \<and> \<not>kralj \<six> \<five> \<and> \<not>kralj \<six> \<six>)) \<and>
                      (kralj \<five> \<six> \<longrightarrow> (\<not>kralj \<five> \<five> \<and> \<not>kralj \<four> \<five> \<and> \<not>kralj \<four> \<six> \<and> \<not>kralj \<six> \<five> \<and> \<not>kralj \<six> \<six>)) \<and>

                      (kralj \<six> \<zero> \<longrightarrow> (\<not>kralj \<six> \<one> \<and> \<not>kralj \<five> \<zero> \<and> \<not>kralj \<five> \<one>)) \<and>
                      (kralj \<six> \<one> \<longrightarrow> (\<not>kralj \<six> \<zero> \<and> \<not>kralj \<six> \<two> \<and> \<not>kralj \<five> \<zero> \<and> \<not>kralj \<five> \<one> \<and> \<not>kralj \<five> \<two>)) \<and>
                      (kralj \<six> \<two> \<longrightarrow> (\<not>kralj \<six> \<one> \<and> \<not>kralj \<six> \<three> \<and> \<not>kralj \<five> \<one> \<and> \<not>kralj \<five> \<two> \<and> \<not>kralj \<five> \<three>)) \<and>
                      (kralj \<six> \<three> \<longrightarrow> (\<not>kralj \<six> \<two> \<and> \<not>kralj \<six> \<four> \<and> \<not>kralj \<five> \<two> \<and> \<not>kralj \<five> \<three> \<and> \<not>kralj \<five> \<four>)) \<and>
                      (kralj \<six> \<four> \<longrightarrow> (\<not>kralj \<six> \<three> \<and> \<not>kralj v \<five> \<and> \<not>kralj \<five> \<three> \<and> \<not>kralj \<five> \<four> \<and> \<not>kralj \<five> \<five>)) \<and>
                      (kralj \<six> \<five> \<longrightarrow> (\<not>kralj \<six> \<four> \<and> \<not>kralj \<six> \<six> \<and> \<not>kralj \<five> \<four> \<and> \<not>kralj \<five> \<five> \<and> \<not>kralj \<five> \<six>)) \<and>
                      (kralj \<six> \<six> \<longrightarrow> (\<not>kralj \<six> \<five> \<and> \<not>kralj \<five> \<five> \<and> \<not>kralj \<five> \<six>))"




begin
text \<open>Neke provere\<close>

(*Pitamo se da li je nas model kontradiktoran.*)
lemma "False"
  oops (*Sledgehammer ne uspeva da pronadje kontradikciju!*)

(*lemma "\<two> \<prec> \<eight>"
  by (metis (full_types) broj.distinct(11) broj.distinct(13) broj.distinct(19) broj.distinct(21) broj.distinct(23) broj.distinct(25) broj.distinct(27) broj.distinct(29) broj.distinct(3) broj.distinct(35) broj.distinct(37) broj.distinct(39) broj.distinct(41) broj.distinct(43) broj.distinct(47) broj.distinct(49) broj.distinct(5) broj.distinct(51) broj.distinct(53) broj.distinct(55) broj.distinct(59) broj.distinct(61) broj.distinct(63) broj.distinct(65)  broj.distinct(69) broj.distinct(7) broj.distinct(71) broj.distinct(73) broj.distinct(77) broj.distinct(79) broj.distinct(83) broj.distinct(87) broj.distinct(9) manje_Sledbenik manje_Trans sledbenik_Eksplicitno)*)



section \<open>Nitpick\<close>

lemma Kombinacija1: "\<not>(
      kralj \<zero> \<zero> = x0_0 \<and> kralj \<zero> \<one> = x0_1 \<and> kralj \<zero> \<two> = x0_2 \<and> kralj \<zero> \<three> = x0_3 \<and> kralj \<zero> \<four> = x0_4 \<and> kralj \<zero> \<five> = x0_5 \<and> kralj \<zero> \<six> = x0_6
      kralj \<one> \<zero> = x1_0 \<and> kralj \<one> \<one> = x1_1 \<and> kralj \<one> \<two> = x1_2 \<and> kralj \<one> \<three> = x1_3 \<and> kralj \<one> \<four> = x1_4 \<and> kralj \<one> \<five> = x1_5 \<and> kralj \<one> \<six> = x1_6
      kralj \<two> \<zero> = x2_0 \<and> kralj \<two> \<one> = x2_1 \<and> kralj \<two> \<two> = x2_2 \<and> kralj \<two> \<three> = x2_3 \<and> kralj \<two> \<four> = x2_4 \<and> kralj \<two> \<five> = x2_5 \<and> kralj \<two> \<six> = x2_6
      kralj \<three> \<zero> = x3_0 \<and> kralj \<three> \<one> = x3_1 \<and> kralj \<three> \<two> = x3_2 \<and> kralj \<three> \<three> = x3_3 \<and> kralj \<three> \<four> = x3_4 \<and> kralj \<three> \<five> = x3_5 \<and> kralj \<three> \<six> = x3_6
      kralj \<four> \<zero> = x4_0 \<and> kralj \<four> \<one> = x4_1 \<and> kralj \<four> \<two> = x4_2 \<and> kralj \<four> \<three> = x4_3 \<and> kralj \<four> \<four> = x4_4 \<and> kralj \<four> \<five> = x4_5 \<and> kralj \<four> \<six> = x4_6
      kralj \<five> \<zero> = x5_0 \<and> kralj \<five> \<one> = x5_1 \<and> kralj \<five> \<two> = x5_2 \<and> kralj \<five> \<three> = x5_3 \<and> kralj \<five> \<four> = x5_4 \<and> kralj \<five> \<five> = x5_5 \<and> kralj \<five> \<six> = x5_6
      kralj \<six> \<zero> = x6_0 \<and> kralj \<six> \<one> = x6_1 \<and> kralj \<six> \<two> = x6_2 \<and> kralj \<six> \<three> = x6_3 \<and> kralj \<six> \<four> = x6_4 \<and> kralj \<six> \<five> = x6_5 \<and> kralj \<six> \<six> = x6_6
      )"

  nitpick[expect=genuine]
  oops


end


end