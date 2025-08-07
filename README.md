# mathcontest-lean

**mathcontest-lean** is a collection of formalized mathematics olympiad problems written in [Lean 4](https://leanprover-community.github.io/). The goal of this project is to rigorously verify solutions to contest problems.

## 🔧 Structure

- `OKTV/` — Problems from the [Hungarian National Secondary School Academic Competition](https://www.oktatas.hu/kozneveles/tanulmanyi_versenyek_/oktv_kereteben/versenyfeladatok_javitasi_utmutatok)
- `AranyDaniel/` — Problems from the [Dániel Arany Secondary School Mathematics Competition](https://www.bolyai.hu/versenyek-arany-daniel-matematikaverseny/)

## ▶️ Trying It Out

You can try out the proofs directly in your browser using the [Lean 4 Web Editor](https://live.lean-lang.org/).  
Just copy and paste the Lean code from this repository into the editor — no installation required.

## ❗ Mistakes in Official Solutions

Sometimes even official solutions contain subtle mistakes. This section tracks such discoveries made during formalization.

|Problem|Official Solution            |Mistake|
|-------|-----------------------------|-------|
|[OKTV2006_I_II_P5](OKTV/OKTV2006_I_II_P5.lean)|[oktatas.hu](https://www.oktatas.hu/pub_bin/dload/kozoktatas/tanulmanyi_versenyek/oktv/oktv_2006_2007/mat1_javut2f_oktv0607.pdf#page=7)|The official solution doesn't check p=19 after discovering that 7 < p and p < 21, luckily it doesn't affect the final result.|

## ✅ List of formalized problems

|Problem|Solved                       |Topics|
|-------|-----------------------------|------|
|[OKTV2024_II_I_P4](OKTV/OKTV2024_II_I_P4.lean)|✅                            |number theory|
|[OKTV2023_I_II_P3](OKTV/OKTV2023_I_II_P3.lean)|✅                            |algebra|
|[OKTV2024_I_II_P3](OKTV/OKTV2024_I_II_P3.lean)|✅                            |functions|
|[OKTV2024_III_I_P3](OKTV/OKTV2024_III_I_P3.lean)|✅                            |functions|
|[OKTV2024_II_II_P4](OKTV/OKTV2024_II_II_P4.lean)|✅                            |functions|
|[OKTV2014_II_I_P3](OKTV/OKTV2014_II_I_P3.lean)|✅                            |functions|
|[OKTV2020_I_II_P2](OKTV/OKTV2020_I_II_P2.lean)|✅                            |functions|
|[OKTV2015_I_II_P3](OKTV/OKTV2015_I_II_P3.lean)|✅                            |inequalities, trigonometry|
|[OKTV2020_III_I_P5](OKTV/OKTV2020_III_I_P5.lean)|✅                            |functions|
|[OKTV2016_III_I_P3](OKTV/OKTV2016_III_I_P3.lean)|✅                            |algebra, trigonometry|
|[OKTV2019_III_I_P3](OKTV/OKTV2019_III_I_P3.lean)|✅                            |algebra|
|[OKTV2009_I_II_P4](OKTV/OKTV2009_I_II_P4.lean)|❌                            |inequalities|
|[OKTV2011_I_I_P1](OKTV/OKTV2011_I_I_P1.lean)|✅                            |algebra|
|[OKTV2012_I_II_P1](OKTV/OKTV2012_I_II_P1.lean)|✅                            |algebra|
|[OKTV2017_I_I_P2](OKTV/OKTV2017_I_I_P2.lean)|✅                            |algebra|
|[OKTV2018_I_III_P1](OKTV/OKTV2018_I_III_P1.lean)|❌                            |number theory|
|[OKTV2018_I_II_P4](OKTV/OKTV2018_I_II_P4.lean)|✅                            |algebra|
|[OKTV2019_I_II_P3](OKTV/OKTV2019_I_II_P3.lean)|✅                            |algebra|
|[OKTV2019_I_I_P5](OKTV/OKTV2019_I_I_P5.lean)|✅                            |algebra|
|[OKTV2020_I_II_P1](OKTV/OKTV2020_I_II_P1.lean)|✅                            |algebra|
|[OKTV2016_II_II_P2](OKTV/OKTV2016_II_II_P2.lean)|❌                            |inequalities|
|[OKTV2009_II_III_P1](OKTV/OKTV2009_II_III_P1.lean)|❌                            |inequalities|
|[OKTV2012_II_I_P1](OKTV/OKTV2012_II_I_P1.lean)|✅                            |algebra|
|[OKTV2017_II_I_P3](OKTV/OKTV2017_II_I_P3.lean)|✅                            |algebra|
|[OKTV2015_II_I_P3](OKTV/OKTV2015_II_I_P3.lean)|✅                            |number theory|
|[OKTV2014_I_I_P4](OKTV/OKTV2014_I_I_P4.lean)|✅                            |algebra|
|[OKTV2014_III_I_P1](OKTV/OKTV2014_III_I_P1.lean)|✅                            |number theory|
|[OKTV2024_I_I_P3](OKTV/OKTV2024_I_I_P3.lean)|✅                            |algebra|
|[OKTV2009_II_I_P3](OKTV/OKTV2009_II_I_P3.lean)|✅                            |algebra|
|[OKTV2011_II_I_P1](OKTV/OKTV2011_II_I_P1.lean)|✅                            |algebra|
|[OKTV2018_II_I_P2](OKTV/OKTV2018_II_I_P2.lean)|✅                            |inequalities|
|[OKTV2019_III_I_P1](OKTV/OKTV2019_III_I_P1.lean)|❌                            |number theory|
|[OKTV2004_I_I_P3](OKTV/OKTV2004_I_I_P3.lean)|✅                            |number theory|
|[OKTV2004_I_I_P4](OKTV/OKTV2004_I_I_P4.lean)|✅                            |number theory|
|[OKTV2010_III_I_P3](OKTV/OKTV2010_III_I_P3.lean)|✅                            |number theory|
|[OKTV2010_II_I_P3](OKTV/OKTV2010_II_I_P3.lean)|✅                            |inequalities|
|[OKTV2018_II_I_P5](OKTV/OKTV2018_II_I_P5.lean)|❌                            |number theory|
|[OKTV2020_II_III_P1](OKTV/OKTV2020_II_III_P1.lean)|✅                            |inequalities|
|[OKTV2015_II_II_P4](OKTV/OKTV2015_II_II_P4.lean)|✅                            |number theory|
|[OKTV2016_II_I_P4](OKTV/OKTV2016_II_I_P4.lean)|✅                            |number theory|
|[OKTV2016_III_III_P3](OKTV/OKTV2016_III_III_P3.lean)|❌                            |number theory|
|[OKTV2020_III_I_P1](OKTV/OKTV2020_III_I_P1.lean)|✅                            |number theory|
|[OKTV2022_I_I_P1](OKTV/OKTV2022_I_I_P1.lean)|✅                            |number theory|
|[OKTV2023_II_I_P4](OKTV/OKTV2023_II_I_P4.lean)|✅                            |number theory|
|[OKTV2013_I_I_P1](OKTV/OKTV2013_I_I_P1.lean)|✅                            |algebra|
|[OKTV2013_I_I_P2](OKTV/OKTV2013_I_I_P2.lean)|✅                            |number theory|
|[OKTV2006_I_II_P5](OKTV/OKTV2006_I_II_P5.lean)|✅                            |number theory|
|[OKTV2010_I_I_P4](OKTV/OKTV2010_I_I_P4.lean)|✅                            |number theory|
|[OKTV2014_I_I_P3](OKTV/OKTV2014_I_I_P3.lean)|✅                            |number theory|
|[OKTV2011_III_I_P3](OKTV/OKTV2011_III_I_P3.lean)|✅                            |number theory|
|[OKTV2018_III_I_P2](OKTV/OKTV2018_III_I_P2.lean)|✅                            |number theory|
|[OKTV2007_II_I_P3](OKTV/OKTV2007_II_I_P3.lean)|✅                            |number theory|
|[OKTV2019_II_II_P3](OKTV/OKTV2019_II_II_P3.lean)|✅                            |number theory|
|[OKTV2016_II_II_P3](OKTV/OKTV2016_II_II_P3.lean)|✅                            |number theory|
|[OKTV2021_II_II_P1](OKTV/OKTV2021_II_II_P1.lean)|✅                            |number theory|
|[OKTV2022_II_II_P4](OKTV/OKTV2022_II_II_P4.lean)|✅                            |number theory|
|[Arany2018_B_III_II_P2](Arany/Arany2018_B_III_II_P2.lean)|✅                            |functions|
|[Arany2012_A_I_I_P3](Arany/Arany2012_A_I_I_P3.lean)|✅                            |number theory|
|[Arany2019_A_III_II_P2](Arany/Arany2019_A_III_II_P2.lean)|✅                            |inequalities|
|[Arany2015_B_III_II_P1](Arany/Arany2015_B_III_II_P1.lean)|✅                            |number theory|
|[Arany1998_B_I_I_P3](Arany/Arany1998_B_I_I_P3.lean)|✅                            |algebra|
|[Arany1998_B_I_I_P1](Arany/Arany1998_B_I_I_P1.lean)|✅                            |number theory|
|[Arany2021_A_II_II_P2](Arany/Arany2021_A_II_II_P2.lean)|❌                            |algebra|
|[Arany2015_B_II_III_P1](Arany/Arany2015_B_II_III_P1.lean)|✅                            |number theory|
|[Arany2014_A_II_I_P3](Arany/Arany2014_A_II_I_P3.lean)|✅                            |number theory|
|[Arany2012_A_II_III_P3](Arany/Arany2012_A_II_III_P3.lean)|✅                            |number theory|
|[Arany2012_B_II_III_P3](Arany/Arany2012_B_II_III_P3.lean)|❌                            |algebra, number theory|
|[Arany2011_A_II_II_P1](Arany/Arany2011_A_II_II_P1.lean)|✅                            |algebra, number theory|
|[Arany2011_A_I_I_P4](Arany/Arany2011_A_I_I_P4.lean)|✅                            |number theory|
|[Arany2011_B_I_I_P3](Arany/Arany2011_B_I_I_P3.lean)|✅                            |number theory|
|[Arany2013_A_II_II_P3](Arany/Arany2013_A_II_II_P3.lean)|✅                            |number theory|
|[Arany2013_B_II_III_P3](Arany/Arany2013_B_II_III_P3.lean)|✅                            |number theory|
|[Arany2013_A_I_II_P2](Arany/Arany2013_A_I_II_P2.lean)|✅                            |number theory|
|[Arany2014_B_I_II_P2](Arany/Arany2014_B_I_II_P2.lean)|✅                            |inequalities|
|[Arany2014_B_I_I_P2](Arany/Arany2014_B_I_I_P2.lean)|✅                            |number theory|
|[Arany2015_A_I_I_P5](Arany/Arany2015_A_I_I_P5.lean)|✅                            |algebra|
|[Arany2016_A_II_III_P3](Arany/Arany2016_A_II_III_P3.lean)|✅                            |algebra|
|[Arany2016_A_II_II_P1](Arany/Arany2016_A_II_II_P1.lean)|✅                            |number theory|
|[Arany2015_A_I_II_P1](Arany/Arany2015_A_I_II_P1.lean)|✅                            |inequalities, number theory|
|[Arany2018_A_III_I_P2](Arany/Arany2018_A_III_I_P2.lean)|✅                            |number theory|
|[Arany2020_A_I_I_P1](Arany/Arany2020_A_I_I_P1.lean)|✅                            |number theory|
|[Arany2020_B_I_II_P1](Arany/Arany2020_B_I_II_P1.lean)|✅                            |number theory|
|[Arany2021_A_III_I_P1](Arany/Arany2021_A_III_I_P1.lean)|✅                            |algebra|
|[Arany2021_B_I_III_P1](Arany/Arany2021_B_I_III_P1.lean)|❌                            |number theory|
|[Arany2022_A_II_III_P1](Arany/Arany2022_A_II_III_P1.lean)|❌                            |number theory|
|[Arany2022_A_III_II_P1](Arany/Arany2022_A_III_II_P1.lean)|✅                            |number theory|
|[Arany2022_A_III_I_P3](Arany/Arany2022_A_III_I_P3.lean)|✅                            |number theory|
|[Arany2022_B_I_I_P3](Arany/Arany2022_B_I_I_P3.lean)|✅                            |number theory|
|[Arany2023_A_III_I_P2](Arany/Arany2023_A_III_I_P2.lean)|✅                            |number theory|
|[Arany2023_A_I_II_P1](Arany/Arany2023_A_I_II_P1.lean)|✅                            |algebra, number theory|
|[Arany2023_A_II_I_P2](Arany/Arany2023_A_II_I_P2.lean)|✅                            |number theory|
|[Arany2023_A_I_I_P3](Arany/Arany2023_A_I_I_P3.lean)|✅                            |algebra|
|[Arany2023_A_I_I_P1](Arany/Arany2023_A_I_I_P1.lean)|✅                            |number theory|
|[Arany2023_B_III_I_P2](Arany/Arany2023_B_III_I_P2.lean)|✅                            |algebra, inequalities|
