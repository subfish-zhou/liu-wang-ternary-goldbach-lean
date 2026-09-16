import LiuWang.Proof.Campaign20260915.RSFiniteExtension.CompletenessCore
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Finite

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

def primesThroughStart : List ℕ := [1423]

theorem span_start : PrimeSpan 1420 1423 primesThroughStart :=
  primeSpan_of_checked complete_start (by decide +kernel)

theorem nodup_start : primesThroughStart.Nodup := by decide +kernel

theorem span_Block000 : PrimeSpan 1423 1439 primes_Block000 :=
  primeSpan_of_checked complete_Block000 (by decide +kernel)

def primesThrough000 : List ℕ := primesThroughStart ++ primes_Block000

theorem span_through000 : PrimeSpan 1420 1439 primesThrough000 :=
  primeSpan_append (by norm_num) (by norm_num) span_start span_Block000

theorem nodup_through000 : primesThrough000.Nodup :=
  primeSpan_nodup_append span_start span_Block000 nodup_start (by decide +kernel)

theorem span_Block001 : PrimeSpan 1439 1601 primes_Block001 :=
  primeSpan_of_checked complete_Block001 (by decide +kernel)

def primesThrough001 : List ℕ := primesThrough000 ++ primes_Block001

theorem span_through001 : PrimeSpan 1420 1601 primesThrough001 :=
  primeSpan_append (by norm_num) (by norm_num) span_through000 span_Block001

theorem nodup_through001 : primesThrough001.Nodup :=
  primeSpan_nodup_append span_through000 span_Block001 nodup_through000 (by decide +kernel)

theorem span_Block002 : PrimeSpan 1601 1783 primes_Block002 :=
  primeSpan_of_checked complete_Block002 (by decide +kernel)

def primesThrough002 : List ℕ := primesThrough001 ++ primes_Block002

theorem span_through002 : PrimeSpan 1420 1783 primesThrough002 :=
  primeSpan_append (by norm_num) (by norm_num) span_through001 span_Block002

theorem nodup_through002 : primesThrough002.Nodup :=
  primeSpan_nodup_append span_through001 span_Block002 nodup_through001 (by decide +kernel)

theorem span_Block003 : PrimeSpan 1783 1987 primes_Block003 :=
  primeSpan_of_checked complete_Block003 (by decide +kernel)

def primesThrough003 : List ℕ := primesThrough002 ++ primes_Block003

theorem span_through003 : PrimeSpan 1420 1987 primesThrough003 :=
  primeSpan_append (by norm_num) (by norm_num) span_through002 span_Block003

theorem nodup_through003 : primesThrough003.Nodup :=
  primeSpan_nodup_append span_through002 span_Block003 nodup_through002 (by decide +kernel)

theorem span_Block004 : PrimeSpan 1987 2143 primes_Block004 :=
  primeSpan_of_checked complete_Block004 (by decide +kernel)

def primesThrough004 : List ℕ := primesThrough003 ++ primes_Block004

theorem span_through004 : PrimeSpan 1420 2143 primesThrough004 :=
  primeSpan_append (by norm_num) (by norm_num) span_through003 span_Block004

theorem nodup_through004 : primesThrough004.Nodup :=
  primeSpan_nodup_append span_through003 span_Block004 nodup_through003 (by decide +kernel)

theorem span_Block005 : PrimeSpan 2143 2347 primes_Block005 :=
  primeSpan_of_checked complete_Block005 (by decide +kernel)

def primesThrough005 : List ℕ := primesThrough004 ++ primes_Block005

theorem span_through005 : PrimeSpan 1420 2347 primesThrough005 :=
  primeSpan_append (by norm_num) (by norm_num) span_through004 span_Block005

theorem nodup_through005 : primesThrough005.Nodup :=
  primeSpan_nodup_append span_through004 span_Block005 nodup_through004 (by decide +kernel)

theorem span_Block006 : PrimeSpan 2347 2543 primes_Block006 :=
  primeSpan_of_checked complete_Block006 (by decide +kernel)

def primesThrough006 : List ℕ := primesThrough005 ++ primes_Block006

theorem span_through006 : PrimeSpan 1420 2543 primesThrough006 :=
  primeSpan_append (by norm_num) (by norm_num) span_through005 span_Block006

theorem nodup_through006 : primesThrough006.Nodup :=
  primeSpan_nodup_append span_through005 span_Block006 nodup_through005 (by decide +kernel)

theorem span_Block007 : PrimeSpan 2543 2713 primes_Block007 :=
  primeSpan_of_checked complete_Block007 (by decide +kernel)

def primesThrough007 : List ℕ := primesThrough006 ++ primes_Block007

theorem span_through007 : PrimeSpan 1420 2713 primesThrough007 :=
  primeSpan_append (by norm_num) (by norm_num) span_through006 span_Block007

theorem nodup_through007 : primesThrough007.Nodup :=
  primeSpan_nodup_append span_through006 span_Block007 nodup_through006 (by decide +kernel)

theorem span_Block008 : PrimeSpan 2713 2903 primes_Block008 :=
  primeSpan_of_checked complete_Block008 (by decide +kernel)

def primesThrough008 : List ℕ := primesThrough007 ++ primes_Block008

theorem span_through008 : PrimeSpan 1420 2903 primesThrough008 :=
  primeSpan_append (by norm_num) (by norm_num) span_through007 span_Block008

theorem nodup_through008 : primesThrough008.Nodup :=
  primeSpan_nodup_append span_through007 span_Block008 nodup_through007 (by decide +kernel)

theorem span_Block009 : PrimeSpan 2903 3119 primes_Block009 :=
  primeSpan_of_checked complete_Block009 (by decide +kernel)

def primesThrough009 : List ℕ := primesThrough008 ++ primes_Block009

theorem span_through009 : PrimeSpan 1420 3119 primesThrough009 :=
  primeSpan_append (by norm_num) (by norm_num) span_through008 span_Block009

theorem nodup_through009 : primesThrough009.Nodup :=
  primeSpan_nodup_append span_through008 span_Block009 nodup_through008 (by decide +kernel)

theorem span_Block010 : PrimeSpan 3119 3323 primes_Block010 :=
  primeSpan_of_checked complete_Block010 (by decide +kernel)

def primesThrough010 : List ℕ := primesThrough009 ++ primes_Block010

theorem span_through010 : PrimeSpan 1420 3323 primesThrough010 :=
  primeSpan_append (by norm_num) (by norm_num) span_through009 span_Block010

theorem nodup_through010 : primesThrough010.Nodup :=
  primeSpan_nodup_append span_through009 span_Block010 nodup_through009 (by decide +kernel)

theorem span_Block011 : PrimeSpan 3323 3527 primes_Block011 :=
  primeSpan_of_checked complete_Block011 (by decide +kernel)

def primesThrough011 : List ℕ := primesThrough010 ++ primes_Block011

theorem span_through011 : PrimeSpan 1420 3527 primesThrough011 :=
  primeSpan_append (by norm_num) (by norm_num) span_through010 span_Block011

theorem nodup_through011 : primesThrough011.Nodup :=
  primeSpan_nodup_append span_through010 span_Block011 nodup_through010 (by decide +kernel)

theorem span_Block012 : PrimeSpan 3527 3697 primes_Block012 :=
  primeSpan_of_checked complete_Block012 (by decide +kernel)

def primesThrough012 : List ℕ := primesThrough011 ++ primes_Block012

theorem span_through012 : PrimeSpan 1420 3697 primesThrough012 :=
  primeSpan_append (by norm_num) (by norm_num) span_through011 span_Block012

theorem nodup_through012 : primesThrough012.Nodup :=
  primeSpan_nodup_append span_through011 span_Block012 nodup_through011 (by decide +kernel)

theorem span_Block013 : PrimeSpan 3697 3907 primes_Block013 :=
  primeSpan_of_checked complete_Block013 (by decide +kernel)

def primesThrough013 : List ℕ := primesThrough012 ++ primes_Block013

theorem span_through013 : PrimeSpan 1420 3907 primesThrough013 :=
  primeSpan_append (by norm_num) (by norm_num) span_through012 span_Block013

theorem nodup_through013 : primesThrough013.Nodup :=
  primeSpan_nodup_append span_through012 span_Block013 nodup_through012 (by decide +kernel)

theorem span_Block014 : PrimeSpan 3907 4093 primes_Block014 :=
  primeSpan_of_checked complete_Block014 (by decide +kernel)

def primesThrough014 : List ℕ := primesThrough013 ++ primes_Block014

theorem span_through014 : PrimeSpan 1420 4093 primesThrough014 :=
  primeSpan_append (by norm_num) (by norm_num) span_through013 span_Block014

theorem nodup_through014 : primesThrough014.Nodup :=
  primeSpan_nodup_append span_through013 span_Block014 nodup_through013 (by decide +kernel)

theorem span_Block015 : PrimeSpan 4093 4283 primes_Block015 :=
  primeSpan_of_checked complete_Block015 (by decide +kernel)

def primesThrough015 : List ℕ := primesThrough014 ++ primes_Block015

theorem span_through015 : PrimeSpan 1420 4283 primesThrough015 :=
  primeSpan_append (by norm_num) (by norm_num) span_through014 span_Block015

theorem nodup_through015 : primesThrough015.Nodup :=
  primeSpan_nodup_append span_through014 span_Block015 nodup_through014 (by decide +kernel)

theorem span_Block016 : PrimeSpan 4283 4513 primes_Block016 :=
  primeSpan_of_checked complete_Block016 (by decide +kernel)

def primesThrough016 : List ℕ := primesThrough015 ++ primes_Block016

theorem span_through016 : PrimeSpan 1420 4513 primesThrough016 :=
  primeSpan_append (by norm_num) (by norm_num) span_through015 span_Block016

theorem nodup_through016 : primesThrough016.Nodup :=
  primeSpan_nodup_append span_through015 span_Block016 nodup_through015 (by decide +kernel)

theorem span_Block017 : PrimeSpan 4513 4721 primes_Block017 :=
  primeSpan_of_checked complete_Block017 (by decide +kernel)

def primesThrough017 : List ℕ := primesThrough016 ++ primes_Block017

theorem span_through017 : PrimeSpan 1420 4721 primesThrough017 :=
  primeSpan_append (by norm_num) (by norm_num) span_through016 span_Block017

theorem nodup_through017 : primesThrough017.Nodup :=
  primeSpan_nodup_append span_through016 span_Block017 nodup_through016 (by decide +kernel)

theorem span_Block018 : PrimeSpan 4721 4937 primes_Block018 :=
  primeSpan_of_checked complete_Block018 (by decide +kernel)

def primesThrough018 : List ℕ := primesThrough017 ++ primes_Block018

theorem span_through018 : PrimeSpan 1420 4937 primesThrough018 :=
  primeSpan_append (by norm_num) (by norm_num) span_through017 span_Block018

theorem nodup_through018 : primesThrough018.Nodup :=
  primeSpan_nodup_append span_through017 span_Block018 nodup_through017 (by decide +kernel)

theorem span_Block019 : PrimeSpan 4937 5113 primes_Block019 :=
  primeSpan_of_checked complete_Block019 (by decide +kernel)

def primesThrough019 : List ℕ := primesThrough018 ++ primes_Block019

theorem span_through019 : PrimeSpan 1420 5113 primesThrough019 :=
  primeSpan_append (by norm_num) (by norm_num) span_through018 span_Block019

theorem nodup_through019 : primesThrough019.Nodup :=
  primeSpan_nodup_append span_through018 span_Block019 nodup_through018 (by decide +kernel)

theorem span_Block020 : PrimeSpan 5113 5351 primes_Block020 :=
  primeSpan_of_checked complete_Block020 (by decide +kernel)

def primesThrough020 : List ℕ := primesThrough019 ++ primes_Block020

theorem span_through020 : PrimeSpan 1420 5351 primesThrough020 :=
  primeSpan_append (by norm_num) (by norm_num) span_through019 span_Block020

theorem nodup_through020 : primesThrough020.Nodup :=
  primeSpan_nodup_append span_through019 span_Block020 nodup_through019 (by decide +kernel)

theorem span_Block021 : PrimeSpan 5351 5531 primes_Block021 :=
  primeSpan_of_checked complete_Block021 (by decide +kernel)

def primesThrough021 : List ℕ := primesThrough020 ++ primes_Block021

theorem span_through021 : PrimeSpan 1420 5531 primesThrough021 :=
  primeSpan_append (by norm_num) (by norm_num) span_through020 span_Block021

theorem nodup_through021 : primesThrough021.Nodup :=
  primeSpan_nodup_append span_through020 span_Block021 nodup_through020 (by decide +kernel)

theorem span_Block022 : PrimeSpan 5531 5743 primes_Block022 :=
  primeSpan_of_checked complete_Block022 (by decide +kernel)

def primesThrough022 : List ℕ := primesThrough021 ++ primes_Block022

theorem span_through022 : PrimeSpan 1420 5743 primesThrough022 :=
  primeSpan_append (by norm_num) (by norm_num) span_through021 span_Block022

theorem nodup_through022 : primesThrough022.Nodup :=
  primeSpan_nodup_append span_through021 span_Block022 nodup_through021 (by decide +kernel)

theorem span_Block023 : PrimeSpan 5743 5939 primes_Block023 :=
  primeSpan_of_checked complete_Block023 (by decide +kernel)

def primesThrough023 : List ℕ := primesThrough022 ++ primes_Block023

theorem span_through023 : PrimeSpan 1420 5939 primesThrough023 :=
  primeSpan_append (by norm_num) (by norm_num) span_through022 span_Block023

theorem nodup_through023 : primesThrough023.Nodup :=
  primeSpan_nodup_append span_through022 span_Block023 nodup_through022 (by decide +kernel)

theorem span_Block024 : PrimeSpan 5939 6173 primes_Block024 :=
  primeSpan_of_checked complete_Block024 (by decide +kernel)

def primesThrough024 : List ℕ := primesThrough023 ++ primes_Block024

theorem span_through024 : PrimeSpan 1420 6173 primesThrough024 :=
  primeSpan_append (by norm_num) (by norm_num) span_through023 span_Block024

theorem nodup_through024 : primesThrough024.Nodup :=
  primeSpan_nodup_append span_through023 span_Block024 nodup_through023 (by decide +kernel)

theorem span_Block025 : PrimeSpan 6173 6359 primes_Block025 :=
  primeSpan_of_checked complete_Block025 (by decide +kernel)

def primesThrough025 : List ℕ := primesThrough024 ++ primes_Block025

theorem span_through025 : PrimeSpan 1420 6359 primesThrough025 :=
  primeSpan_append (by norm_num) (by norm_num) span_through024 span_Block025

theorem nodup_through025 : primesThrough025.Nodup :=
  primeSpan_nodup_append span_through024 span_Block025 nodup_through024 (by decide +kernel)

theorem span_Block026 : PrimeSpan 6359 6581 primes_Block026 :=
  primeSpan_of_checked complete_Block026 (by decide +kernel)

def primesThrough026 : List ℕ := primesThrough025 ++ primes_Block026

theorem span_through026 : PrimeSpan 1420 6581 primesThrough026 :=
  primeSpan_append (by norm_num) (by norm_num) span_through025 span_Block026

theorem nodup_through026 : primesThrough026.Nodup :=
  primeSpan_nodup_append span_through025 span_Block026 nodup_through025 (by decide +kernel)

theorem span_Block027 : PrimeSpan 6581 6803 primes_Block027 :=
  primeSpan_of_checked complete_Block027 (by decide +kernel)

def primesThrough027 : List ℕ := primesThrough026 ++ primes_Block027

theorem span_through027 : PrimeSpan 1420 6803 primesThrough027 :=
  primeSpan_append (by norm_num) (by norm_num) span_through026 span_Block027

theorem nodup_through027 : primesThrough027.Nodup :=
  primeSpan_nodup_append span_through026 span_Block027 nodup_through026 (by decide +kernel)

theorem span_Block028 : PrimeSpan 6803 6997 primes_Block028 :=
  primeSpan_of_checked complete_Block028 (by decide +kernel)

def primesThrough028 : List ℕ := primesThrough027 ++ primes_Block028

theorem span_through028 : PrimeSpan 1420 6997 primesThrough028 :=
  primeSpan_append (by norm_num) (by norm_num) span_through027 span_Block028

theorem nodup_through028 : primesThrough028.Nodup :=
  primeSpan_nodup_append span_through027 span_Block028 nodup_through027 (by decide +kernel)

theorem span_Block029 : PrimeSpan 6997 7229 primes_Block029 :=
  primeSpan_of_checked complete_Block029 (by decide +kernel)

def primesThrough029 : List ℕ := primesThrough028 ++ primes_Block029

theorem span_through029 : PrimeSpan 1420 7229 primesThrough029 :=
  primeSpan_append (by norm_num) (by norm_num) span_through028 span_Block029

theorem nodup_through029 : primesThrough029.Nodup :=
  primeSpan_nodup_append span_through028 span_Block029 nodup_through028 (by decide +kernel)

theorem span_Block030 : PrimeSpan 7229 7487 primes_Block030 :=
  primeSpan_of_checked complete_Block030 (by decide +kernel)

def primesThrough030 : List ℕ := primesThrough029 ++ primes_Block030

theorem span_through030 : PrimeSpan 1420 7487 primesThrough030 :=
  primeSpan_append (by norm_num) (by norm_num) span_through029 span_Block030

theorem nodup_through030 : primesThrough030.Nodup :=
  primeSpan_nodup_append span_through029 span_Block030 nodup_through029 (by decide +kernel)

theorem span_Block031 : PrimeSpan 7487 7669 primes_Block031 :=
  primeSpan_of_checked complete_Block031 (by decide +kernel)

def primesThrough031 : List ℕ := primesThrough030 ++ primes_Block031

theorem span_through031 : PrimeSpan 1420 7669 primesThrough031 :=
  primeSpan_append (by norm_num) (by norm_num) span_through030 span_Block031

theorem nodup_through031 : primesThrough031.Nodup :=
  primeSpan_nodup_append span_through030 span_Block031 nodup_through030 (by decide +kernel)

theorem span_Block032 : PrimeSpan 7669 7879 primes_Block032 :=
  primeSpan_of_checked complete_Block032 (by decide +kernel)

def primesThrough032 : List ℕ := primesThrough031 ++ primes_Block032

theorem span_through032 : PrimeSpan 1420 7879 primesThrough032 :=
  primeSpan_append (by norm_num) (by norm_num) span_through031 span_Block032

theorem nodup_through032 : primesThrough032.Nodup :=
  primeSpan_nodup_append span_through031 span_Block032 nodup_through031 (by decide +kernel)

theorem span_Block033 : PrimeSpan 7879 8111 primes_Block033 :=
  primeSpan_of_checked complete_Block033 (by decide +kernel)

def primesThrough033 : List ℕ := primesThrough032 ++ primes_Block033

theorem span_through033 : PrimeSpan 1420 8111 primesThrough033 :=
  primeSpan_append (by norm_num) (by norm_num) span_through032 span_Block033

theorem nodup_through033 : primesThrough033.Nodup :=
  primeSpan_nodup_append span_through032 span_Block033 nodup_through032 (by decide +kernel)

theorem span_Block034 : PrimeSpan 8111 8317 primes_Block034 :=
  primeSpan_of_checked complete_Block034 (by decide +kernel)

def primesThrough034 : List ℕ := primesThrough033 ++ primes_Block034

theorem span_through034 : PrimeSpan 1420 8317 primesThrough034 :=
  primeSpan_append (by norm_num) (by norm_num) span_through033 span_Block034

theorem nodup_through034 : primesThrough034.Nodup :=
  primeSpan_nodup_append span_through033 span_Block034 nodup_through033 (by decide +kernel)

theorem span_Block035 : PrimeSpan 8317 8573 primes_Block035 :=
  primeSpan_of_checked complete_Block035 (by decide +kernel)

def primesThrough035 : List ℕ := primesThrough034 ++ primes_Block035

theorem span_through035 : PrimeSpan 1420 8573 primesThrough035 :=
  primeSpan_append (by norm_num) (by norm_num) span_through034 span_Block035

theorem nodup_through035 : primesThrough035.Nodup :=
  primeSpan_nodup_append span_through034 span_Block035 nodup_through034 (by decide +kernel)

theorem span_Block036 : PrimeSpan 8573 8753 primes_Block036 :=
  primeSpan_of_checked complete_Block036 (by decide +kernel)

def primesThrough036 : List ℕ := primesThrough035 ++ primes_Block036

theorem span_through036 : PrimeSpan 1420 8753 primesThrough036 :=
  primeSpan_append (by norm_num) (by norm_num) span_through035 span_Block036

theorem nodup_through036 : primesThrough036.Nodup :=
  primeSpan_nodup_append span_through035 span_Block036 nodup_through035 (by decide +kernel)

theorem span_Block037 : PrimeSpan 8753 8971 primes_Block037 :=
  primeSpan_of_checked complete_Block037 (by decide +kernel)

def primesThrough037 : List ℕ := primesThrough036 ++ primes_Block037

theorem span_through037 : PrimeSpan 1420 8971 primesThrough037 :=
  primeSpan_append (by norm_num) (by norm_num) span_through036 span_Block037

theorem nodup_through037 : primesThrough037.Nodup :=
  primeSpan_nodup_append span_through036 span_Block037 nodup_through036 (by decide +kernel)

theorem span_Block038 : PrimeSpan 8971 9199 primes_Block038 :=
  primeSpan_of_checked complete_Block038 (by decide +kernel)

def primesThrough038 : List ℕ := primesThrough037 ++ primes_Block038

theorem span_through038 : PrimeSpan 1420 9199 primesThrough038 :=
  primeSpan_append (by norm_num) (by norm_num) span_through037 span_Block038

theorem nodup_through038 : primesThrough038.Nodup :=
  primeSpan_nodup_append span_through037 span_Block038 nodup_through037 (by decide +kernel)

theorem span_Block039 : PrimeSpan 9199 9413 primes_Block039 :=
  primeSpan_of_checked complete_Block039 (by decide +kernel)

def primesThrough039 : List ℕ := primesThrough038 ++ primes_Block039

theorem span_through039 : PrimeSpan 1420 9413 primesThrough039 :=
  primeSpan_append (by norm_num) (by norm_num) span_through038 span_Block039

theorem nodup_through039 : primesThrough039.Nodup :=
  primeSpan_nodup_append span_through038 span_Block039 nodup_through038 (by decide +kernel)

theorem span_Block040 : PrimeSpan 9413 9623 primes_Block040 :=
  primeSpan_of_checked complete_Block040 (by decide +kernel)

def primesThrough040 : List ℕ := primesThrough039 ++ primes_Block040

theorem span_through040 : PrimeSpan 1420 9623 primesThrough040 :=
  primeSpan_append (by norm_num) (by norm_num) span_through039 span_Block040

theorem nodup_through040 : primesThrough040.Nodup :=
  primeSpan_nodup_append span_through039 span_Block040 nodup_through039 (by decide +kernel)

theorem span_Block041 : PrimeSpan 9623 9829 primes_Block041 :=
  primeSpan_of_checked complete_Block041 (by decide +kernel)

def primesThrough041 : List ℕ := primesThrough040 ++ primes_Block041

theorem span_through041 : PrimeSpan 1420 9829 primesThrough041 :=
  primeSpan_append (by norm_num) (by norm_num) span_through040 span_Block041

theorem nodup_through041 : primesThrough041.Nodup :=
  primeSpan_nodup_append span_through040 span_Block041 nodup_through040 (by decide +kernel)

theorem span_Block042 : PrimeSpan 9829 10069 primes_Block042 :=
  primeSpan_of_checked complete_Block042 (by decide +kernel)

def primesThrough042 : List ℕ := primesThrough041 ++ primes_Block042

theorem span_through042 : PrimeSpan 1420 10069 primesThrough042 :=
  primeSpan_append (by norm_num) (by norm_num) span_through041 span_Block042

theorem nodup_through042 : primesThrough042.Nodup :=
  primeSpan_nodup_append span_through041 span_Block042 nodup_through041 (by decide +kernel)

theorem span_Block043 : PrimeSpan 10069 10271 primes_Block043 :=
  primeSpan_of_checked complete_Block043 (by decide +kernel)

def primesThrough043 : List ℕ := primesThrough042 ++ primes_Block043

theorem span_through043 : PrimeSpan 1420 10271 primesThrough043 :=
  primeSpan_append (by norm_num) (by norm_num) span_through042 span_Block043

theorem nodup_through043 : primesThrough043.Nodup :=
  primeSpan_nodup_append span_through042 span_Block043 nodup_through042 (by decide +kernel)

theorem span_Block044 : PrimeSpan 10271 10499 primes_Block044 :=
  primeSpan_of_checked complete_Block044 (by decide +kernel)

def primesThrough044 : List ℕ := primesThrough043 ++ primes_Block044

theorem span_through044 : PrimeSpan 1420 10499 primesThrough044 :=
  primeSpan_append (by norm_num) (by norm_num) span_through043 span_Block044

theorem nodup_through044 : primesThrough044.Nodup :=
  primeSpan_nodup_append span_through043 span_Block044 nodup_through043 (by decide +kernel)

theorem span_Block045 : PrimeSpan 10499 10729 primes_Block045 :=
  primeSpan_of_checked complete_Block045 (by decide +kernel)

def primesThrough045 : List ℕ := primesThrough044 ++ primes_Block045

theorem span_through045 : PrimeSpan 1420 10729 primesThrough045 :=
  primeSpan_append (by norm_num) (by norm_num) span_through044 span_Block045

theorem nodup_through045 : primesThrough045.Nodup :=
  primeSpan_nodup_append span_through044 span_Block045 nodup_through044 (by decide +kernel)

theorem span_Block046 : PrimeSpan 10729 10973 primes_Block046 :=
  primeSpan_of_checked complete_Block046 (by decide +kernel)

def primesThrough046 : List ℕ := primesThrough045 ++ primes_Block046

theorem span_through046 : PrimeSpan 1420 10973 primesThrough046 :=
  primeSpan_append (by norm_num) (by norm_num) span_through045 span_Block046

theorem nodup_through046 : primesThrough046.Nodup :=
  primeSpan_nodup_append span_through045 span_Block046 nodup_through045 (by decide +kernel)

theorem span_Block047 : PrimeSpan 10973 11197 primes_Block047 :=
  primeSpan_of_checked complete_Block047 (by decide +kernel)

def primesThrough047 : List ℕ := primesThrough046 ++ primes_Block047

theorem span_through047 : PrimeSpan 1420 11197 primesThrough047 :=
  primeSpan_append (by norm_num) (by norm_num) span_through046 span_Block047

theorem nodup_through047 : primesThrough047.Nodup :=
  primeSpan_nodup_append span_through046 span_Block047 nodup_through046 (by decide +kernel)

theorem span_Block048 : PrimeSpan 11197 11443 primes_Block048 :=
  primeSpan_of_checked complete_Block048 (by decide +kernel)

def primesThrough048 : List ℕ := primesThrough047 ++ primes_Block048

theorem span_through048 : PrimeSpan 1420 11443 primesThrough048 :=
  primeSpan_append (by norm_num) (by norm_num) span_through047 span_Block048

theorem nodup_through048 : primesThrough048.Nodup :=
  primeSpan_nodup_append span_through047 span_Block048 nodup_through047 (by decide +kernel)

theorem span_Block049 : PrimeSpan 11443 11699 primes_Block049 :=
  primeSpan_of_checked complete_Block049 (by decide +kernel)

def primesThrough049 : List ℕ := primesThrough048 ++ primes_Block049

theorem span_through049 : PrimeSpan 1420 11699 primesThrough049 :=
  primeSpan_append (by norm_num) (by norm_num) span_through048 span_Block049

theorem nodup_through049 : primesThrough049.Nodup :=
  primeSpan_nodup_append span_through048 span_Block049 nodup_through048 (by decide +kernel)

theorem span_Block050 : PrimeSpan 11699 11923 primes_Block050 :=
  primeSpan_of_checked complete_Block050 (by decide +kernel)

def primesThrough050 : List ℕ := primesThrough049 ++ primes_Block050

theorem span_through050 : PrimeSpan 1420 11923 primesThrough050 :=
  primeSpan_append (by norm_num) (by norm_num) span_through049 span_Block050

theorem nodup_through050 : primesThrough050.Nodup :=
  primeSpan_nodup_append span_through049 span_Block050 nodup_through049 (by decide +kernel)

theorem span_Block051 : PrimeSpan 11923 12119 primes_Block051 :=
  primeSpan_of_checked complete_Block051 (by decide +kernel)

def primesThrough051 : List ℕ := primesThrough050 ++ primes_Block051

theorem span_through051 : PrimeSpan 1420 12119 primesThrough051 :=
  primeSpan_append (by norm_num) (by norm_num) span_through050 span_Block051

theorem nodup_through051 : primesThrough051.Nodup :=
  primeSpan_nodup_append span_through050 span_Block051 nodup_through050 (by decide +kernel)

theorem span_Block052 : PrimeSpan 12119 12373 primes_Block052 :=
  primeSpan_of_checked complete_Block052 (by decide +kernel)

def primesThrough052 : List ℕ := primesThrough051 ++ primes_Block052

theorem span_through052 : PrimeSpan 1420 12373 primesThrough052 :=
  primeSpan_append (by norm_num) (by norm_num) span_through051 span_Block052

theorem nodup_through052 : primesThrough052.Nodup :=
  primeSpan_nodup_append span_through051 span_Block052 nodup_through051 (by decide +kernel)

theorem span_Block053 : PrimeSpan 12373 12553 primes_Block053 :=
  primeSpan_of_checked complete_Block053 (by decide +kernel)

def primesThrough053 : List ℕ := primesThrough052 ++ primes_Block053

theorem span_through053 : PrimeSpan 1420 12553 primesThrough053 :=
  primeSpan_append (by norm_num) (by norm_num) span_through052 span_Block053

theorem nodup_through053 : primesThrough053.Nodup :=
  primeSpan_nodup_append span_through052 span_Block053 nodup_through052 (by decide +kernel)

theorem span_Block054 : PrimeSpan 12553 12781 primes_Block054 :=
  primeSpan_of_checked complete_Block054 (by decide +kernel)

def primesThrough054 : List ℕ := primesThrough053 ++ primes_Block054

theorem span_through054 : PrimeSpan 1420 12781 primesThrough054 :=
  primeSpan_append (by norm_num) (by norm_num) span_through053 span_Block054

theorem nodup_through054 : primesThrough054.Nodup :=
  primeSpan_nodup_append span_through053 span_Block054 nodup_through053 (by decide +kernel)

theorem span_Block055 : PrimeSpan 12781 13001 primes_Block055 :=
  primeSpan_of_checked complete_Block055 (by decide +kernel)

def primesThrough055 : List ℕ := primesThrough054 ++ primes_Block055

theorem span_through055 : PrimeSpan 1420 13001 primesThrough055 :=
  primeSpan_append (by norm_num) (by norm_num) span_through054 span_Block055

theorem nodup_through055 : primesThrough055.Nodup :=
  primeSpan_nodup_append span_through054 span_Block055 nodup_through054 (by decide +kernel)

theorem span_Block056 : PrimeSpan 13001 13219 primes_Block056 :=
  primeSpan_of_checked complete_Block056 (by decide +kernel)

def primesThrough056 : List ℕ := primesThrough055 ++ primes_Block056

theorem span_through056 : PrimeSpan 1420 13219 primesThrough056 :=
  primeSpan_append (by norm_num) (by norm_num) span_through055 span_Block056

theorem nodup_through056 : primesThrough056.Nodup :=
  primeSpan_nodup_append span_through055 span_Block056 nodup_through055 (by decide +kernel)

theorem span_Block057 : PrimeSpan 13219 13463 primes_Block057 :=
  primeSpan_of_checked complete_Block057 (by decide +kernel)

def primesThrough057 : List ℕ := primesThrough056 ++ primes_Block057

theorem span_through057 : PrimeSpan 1420 13463 primesThrough057 :=
  primeSpan_append (by norm_num) (by norm_num) span_through056 span_Block057

theorem nodup_through057 : primesThrough057.Nodup :=
  primeSpan_nodup_append span_through056 span_Block057 nodup_through056 (by decide +kernel)

theorem span_Block058 : PrimeSpan 13463 13697 primes_Block058 :=
  primeSpan_of_checked complete_Block058 (by decide +kernel)

def primesThrough058 : List ℕ := primesThrough057 ++ primes_Block058

theorem span_through058 : PrimeSpan 1420 13697 primesThrough058 :=
  primeSpan_append (by norm_num) (by norm_num) span_through057 span_Block058

theorem nodup_through058 : primesThrough058.Nodup :=
  primeSpan_nodup_append span_through057 span_Block058 nodup_through057 (by decide +kernel)

theorem span_Block059 : PrimeSpan 13697 13907 primes_Block059 :=
  primeSpan_of_checked complete_Block059 (by decide +kernel)

def primesThrough059 : List ℕ := primesThrough058 ++ primes_Block059

theorem span_through059 : PrimeSpan 1420 13907 primesThrough059 :=
  primeSpan_append (by norm_num) (by norm_num) span_through058 span_Block059

theorem nodup_through059 : primesThrough059.Nodup :=
  primeSpan_nodup_append span_through058 span_Block059 nodup_through058 (by decide +kernel)

theorem span_Block060 : PrimeSpan 13907 14173 primes_Block060 :=
  primeSpan_of_checked complete_Block060 (by decide +kernel)

def primesThrough060 : List ℕ := primesThrough059 ++ primes_Block060

theorem span_through060 : PrimeSpan 1420 14173 primesThrough060 :=
  primeSpan_append (by norm_num) (by norm_num) span_through059 span_Block060

theorem nodup_through060 : primesThrough060.Nodup :=
  primeSpan_nodup_append span_through059 span_Block060 nodup_through059 (by decide +kernel)

theorem span_Block061 : PrimeSpan 14173 14431 primes_Block061 :=
  primeSpan_of_checked complete_Block061 (by decide +kernel)

def primesThrough061 : List ℕ := primesThrough060 ++ primes_Block061

theorem span_through061 : PrimeSpan 1420 14431 primesThrough061 :=
  primeSpan_append (by norm_num) (by norm_num) span_through060 span_Block061

theorem nodup_through061 : primesThrough061.Nodup :=
  primeSpan_nodup_append span_through060 span_Block061 nodup_through060 (by decide +kernel)

theorem span_Block062 : PrimeSpan 14431 14653 primes_Block062 :=
  primeSpan_of_checked complete_Block062 (by decide +kernel)

def primesThrough062 : List ℕ := primesThrough061 ++ primes_Block062

theorem span_through062 : PrimeSpan 1420 14653 primesThrough062 :=
  primeSpan_append (by norm_num) (by norm_num) span_through061 span_Block062

theorem nodup_through062 : primesThrough062.Nodup :=
  primeSpan_nodup_append span_through061 span_Block062 nodup_through061 (by decide +kernel)

theorem span_Block063 : PrimeSpan 14653 14851 primes_Block063 :=
  primeSpan_of_checked complete_Block063 (by decide +kernel)

def primesThrough063 : List ℕ := primesThrough062 ++ primes_Block063

theorem span_through063 : PrimeSpan 1420 14851 primesThrough063 :=
  primeSpan_append (by norm_num) (by norm_num) span_through062 span_Block063

theorem nodup_through063 : primesThrough063.Nodup :=
  primeSpan_nodup_append span_through062 span_Block063 nodup_through062 (by decide +kernel)

theorem span_Block064 : PrimeSpan 14851 15101 primes_Block064 :=
  primeSpan_of_checked complete_Block064 (by decide +kernel)

def primesThrough064 : List ℕ := primesThrough063 ++ primes_Block064

theorem span_through064 : PrimeSpan 1420 15101 primesThrough064 :=
  primeSpan_append (by norm_num) (by norm_num) span_through063 span_Block064

theorem nodup_through064 : primesThrough064.Nodup :=
  primeSpan_nodup_append span_through063 span_Block064 nodup_through063 (by decide +kernel)

theorem span_Block065 : PrimeSpan 15101 15307 primes_Block065 :=
  primeSpan_of_checked complete_Block065 (by decide +kernel)

def primesThrough065 : List ℕ := primesThrough064 ++ primes_Block065

theorem span_through065 : PrimeSpan 1420 15307 primesThrough065 :=
  primeSpan_append (by norm_num) (by norm_num) span_through064 span_Block065

theorem nodup_through065 : primesThrough065.Nodup :=
  primeSpan_nodup_append span_through064 span_Block065 nodup_through064 (by decide +kernel)

theorem span_Block066 : PrimeSpan 15307 15527 primes_Block066 :=
  primeSpan_of_checked complete_Block066 (by decide +kernel)

def primesThrough066 : List ℕ := primesThrough065 ++ primes_Block066

theorem span_through066 : PrimeSpan 1420 15527 primesThrough066 :=
  primeSpan_append (by norm_num) (by norm_num) span_through065 span_Block066

theorem nodup_through066 : primesThrough066.Nodup :=
  primeSpan_nodup_append span_through065 span_Block066 nodup_through065 (by decide +kernel)

theorem span_Block067 : PrimeSpan 15527 15739 primes_Block067 :=
  primeSpan_of_checked complete_Block067 (by decide +kernel)

def primesThrough067 : List ℕ := primesThrough066 ++ primes_Block067

theorem span_through067 : PrimeSpan 1420 15739 primesThrough067 :=
  primeSpan_append (by norm_num) (by norm_num) span_through066 span_Block067

theorem nodup_through067 : primesThrough067.Nodup :=
  primeSpan_nodup_append span_through066 span_Block067 nodup_through066 (by decide +kernel)

theorem span_Block068 : PrimeSpan 15739 15971 primes_Block068 :=
  primeSpan_of_checked complete_Block068 (by decide +kernel)

def primesThrough068 : List ℕ := primesThrough067 ++ primes_Block068

theorem span_through068 : PrimeSpan 1420 15971 primesThrough068 :=
  primeSpan_append (by norm_num) (by norm_num) span_through067 span_Block068

theorem nodup_through068 : primesThrough068.Nodup :=
  primeSpan_nodup_append span_through067 span_Block068 nodup_through067 (by decide +kernel)

theorem span_Block069 : PrimeSpan 15971 15991 primes_Block069 :=
  primeSpan_of_checked complete_Block069 (by decide +kernel)

def primesThrough069 : List ℕ := primesThrough068 ++ primes_Block069

theorem span_through069 : PrimeSpan 1420 15991 primesThrough069 :=
  primeSpan_append (by norm_num) (by norm_num) span_through068 span_Block069

theorem nodup_through069 : primesThrough069.Nodup :=
  primeSpan_nodup_append span_through068 span_Block069 nodup_through068 (by decide +kernel)

def extensionPrimes : List ℕ := primesThrough069

theorem extensionPrimes_complete : PrimeSpan 1420 16000 extensionPrimes := by
  intro p
  change p ∈ primesThrough069 ↔ 1420 < p ∧ p ≤ 16000 ∧ p.Prime
  rw [span_through069 p]
  constructor
  · rintro ⟨ha, hb, hp⟩
    exact ⟨ha, by omega, hp⟩
  · rintro ⟨ha, hb, hp⟩
    refine ⟨ha, ?_, hp⟩
    by_contra! hn
    exact gap_15991_16001 p (Finset.mem_Ioo.mpr ⟨hn, by omega⟩) hp

theorem extensionPrimes_nodup : extensionPrimes.Nodup := nodup_through069

theorem extensionPrimes_length : extensionPrimes.length = 1639 := by decide +kernel

theorem primesLE_16000_eq :
    Nat.primesLE 16000 = Nat.primesLE 1420 ∪ extensionPrimes.toFinset :=
  primeSpan_primesLE (by norm_num) extensionPrimes_complete

#print axioms extensionPrimes_complete
#print axioms extensionPrimes_nodup
#print axioms primesLE_16000_eq

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
