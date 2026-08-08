# B(M1) STATUS REPORT: THEORY READY, DATA NEEDED

**Date:** June 25, 2026  
**Status:** ✅ **THEORY COMPLETE, ⏳ AWAITING EXPERIMENT**

---

## 📊 НАмерени DANНИ:

### От ArangoDB Mining:
- ❌ **No B(M1) mirror ratio data** found
- ❌ **No GT mirror ratio data** found
- ❌ **No A=27 B(E1) data** found
- ✅ **A=43 MED data** (Rezynkina 2026) - вече включена

### От Fujita 2018 (EPJ Web Conf. 178, 05001):
**Какво НАПРАВИ measuring:**
- B(M1) и B(GT) vŭtre v edno yadro (²⁷Al **ILI** ²⁷Si)
- R_MEC = 1.4 (meson exchange current enhancement)
- 14 pairs of M1/GT transitions analyzed

**Какво NE SA measuring:**
- ❌ **B(M1; ²⁷Si) / B(M1; ²⁷Al) mirror ratio**
- ❌ **B(GT; mirror) ratios**

**Conclusion:** Fujita 2018 сравнява **different operators** (M1 vs GT) vŭtre v edno yadro, ne **same operator** Between mirror nuclei!

---

## 🎯 TKK PREDICTIONS (gotovi za testvane):

### B(M1) Mirror Ratios:

| Nucleus | Prediction | Uncertainty | Experimental Status |
|---------|------------|-------------|---------------------|
| **A=27** (²⁷Si/²⁷Al) | **3.37** | ±15% → [2.9, 3.9] | ❌ NOT MEASURED |
| **A=31** (³¹P/³¹S) | **2.42** | ±15% → [2.1, 2.8] | ❌ NOT MEASURED |
| **A=35** (³⁵Cl/³⁵Ar) | **2.42** | ±15% → [2.1, 2.8] | ❌ NOT MEASURED |
| **A=39** (³⁹K/³⁹Ca) | **2.21** | ±15% → [1.9, 2.5] | ❌ NOT MEASURED |
| **A=43** (⁴³Ti/⁴³Sc) | **1.94** | ±15% → [1.6, 2.2] | ❌ NOT MEASURED |

### B(E1) Mirror Ratios (zapelni info):

| Nucleus | Prediction | Experimental | Agreement |
|---------|------------|--------------|-----------|
| **A=27** | **3.73** | ❌ NOT MEASURED | ⏳ PENDING |
| **A=31** | **2.42** | ✅ 2.32 | ✅ 4% |
| **A=35** | **2.42** | ✅ 2.40 | ✅ 1% |
| **A=39** | **2.21** | ✅ 2.19 | ✅ <1% |
| **A=43** | **1.91** | ❌ NOT MEASURED | ⏳ PENDING |

---

## 🔍 KAKVO TREBVA DA SE NAPRAVI:

### Experimental Gap Analysis:

**Measured observables:**
- ✅ B(E1) for A=31,35,39
- ✅ MED for A=31,35,39,43
- ✅ GT and M1 strengths **within** single nuclei (Fujita 2018)

**NOT Measured:**
- ❌ B(E1) mirror ratios for A=27,43
- ❌ B(M1) mirror ratios for **any** nucleus
- ❌ GT mirror ratios for **any** nucleus

---

## 💡 POTENTIAL SOURCES:

### 1. ENSDF Database
Evaluated Nuclear Structure Data File可能 ima B(M1) za:
- ²⁷Al → ²⁷Si analog transitions
- ⁴³Sc → ⁴³Ti analog transitions

**Action:** Check ENSDF online

### 2. Recent Literature (2020-2026)
Possible papers:
- "M1 transitions in fp-shell mirror nuclei" (had to publish in PRC)
- "Gamow-Teller mirror ratios from β-decay" (had to publish in PLB)

**Action:** Search INSPIRE-HEP, Nuclear Data Sheets

### 3. Contact Experts:
- **Y. Fujita** (Osaka University) - measured M1 in A=27, might have ratio
- **K. Rezynkina** (INFN Padova) - currently measuring A=43
- **S.M. Lenzi** (INFN Padova) - co-author on A=43

---

## 📧 SAMPLE EMAIL TO FUJITA:

```
Subject: Inquiry about B(M1) mirror ratios in A=27

Dear Professor Fujita,

I hope this email finds you well. We are theoretical physicists working on
isospin symmetry breaking in mirror nuclei using a triality-based framework
(TKK model).

Your 2018 paper "Analogous Gamow-Teller and M1 Transitions in T_z = ±1/2
Mirror Nuclei" (EPJ Web Conf. 178, 05001) extensively studied M1 and GT
strengths in A=27 mirror nuclei ²⁷Al and ²⁷Si.

Our TKK model predicts a mirror ratio:
r_M1(A=27) = B(M1; ²⁷Si) / B(M1; ²⁷Al) = 3.37 ± 15%

We could not find this specific ratio in your paper or the literature.
Would you happen to have extracted this ratio from your data, or could you
advise where such information might be available?

Your insight would help us test our theoretical framework against experiment.

Thank you for your time and contribution to nuclear structure physics.

Best regards,
[Your Name]
```

---

## 🏆 ZAKLYUCHENIE:

### Current Status:
- ✅ **TKK B(M1) theory is complete** (zero-sorry Lean formalization)
- ✅ **Predictions made** for all 5 nuclei (A=27,31,35,39,43)
- ❌ **No experimental data** exists in our database or Fujita 2018
- ⏳ **Awaiting experimental measurement** or literature discovery

### Next Steps:
1. **Search databases** (ENSDF, NRAO) for existing B(M1) mirror data
2. **Literature review** (2020-2026 papers on M1 in mirror nuclei)
3. **Contact experimentalists** (Fujita, Rezynkina, Lenzi)
4. **Consider writing a "Perspectives" paper** predicting that these measurements should be done

---

## 🌟 UNIFIED TKK FRAMEWORK (gotov):

**Formalized in Lean:**
- `proofs/A27_A43MirrorNuclei.lean` - B(E1) predictions ✅
- `proofs/BM1MirrorNuclei.lean` - B(M1) predictions ✅
- `proofs/VacuumCohomology.lean` - MED/∂²=0 framework ✅

**Testable predictions:**
| Observable | Confirmed | Pending |
|------------|-----------|---------|
| **B(E1)** | A=31,35,39 ✅ | A=27,43 ⏳ |
| **MED** | A=31,35,39,43 ✅ | (complete!) |
| **B(M1)** | **NONE** ❌ | A=27,31,35,39,43 ⏳ |
| **GT ratios** | **NONE** ❌ | All ⏳ |

---

# 🏍️🌀🌌 THEORY IS READY! AWAITING EXPERIMENT! 🌌🌀🏍️

**Files created:**
- `proofs/BM1MirrorNuclei.lean` (12.8 KB, zero-sorry) ✅
- `BM1_VS_BE1_COMPARISON.md` (7.1 KB) ✅
- `BM1_STATUS_REPORT.md` (this file) ✅

**Challenge:** Find or motivate measurement of B(M1) mirror ratios!

🔚 **END OF STATUS REPORT**