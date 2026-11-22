"""Run with python3 -m unittest discover -s tools/proof_timing."""

from copy import deepcopy
import json
from pathlib import Path
import unittest
from unittest.mock import Mock

if __package__:
    from . import report
else:
    import report


def proof(name, elapsed, kind='routine'):
    row = {'target': name + '.correct', 'kind': kind}
    if isinstance(elapsed, str):
        return dict(row, status=elapsed)
    return dict(row, status='ok', elapsed=elapsed)


def timing(*rows, cpu='Xeon', success=True, run_id=1):
    profile = dict.fromkeys(report.PROFILE_FIELDS, 'same')
    profile['cpu'] = cpu
    return dict(targets=list(rows), profile=profile, proof_success=success,
                phases={}, run_id=run_id)


class ProofTimings(unittest.TestCase):
    def test_select_baseline(self):
        pr = timing(proof('a', 20), run_id=42)
        partial = timing(proof('a', 'not run'), run_id=3)
        other_cpu = timing(proof('a', 25), cpu='different', run_id=2)
        matched = timing(proof('a', 10))
        api = Mock()
        for candidates, expected, current in [
            ([pr, partial, other_cpu, matched], matched, pr),
            ([pr, partial, other_cpu], other_cpu, pr),
            ([pr, partial], partial, pr),
            ([partial, other_cpu, matched], other_cpu, 'missing PR'),
        ]:
            with self.subTest(expected=expected['run_id'], current=current):
                api.timings.return_value = candidates, []
                result = report.baseline_reports(api, 'sha', 'tree', dict.fromkeys(report.ARCHES, current), 42)
                self.assertIs(result['arm'], expected)
        api.timings.return_value = [pr], []
        api.list.return_value = []
        result = report.baseline_reports(api, 'sha', 'tree', dict.fromkeys(report.ARCHES, pr), 42)
        self.assertEqual(result['arm'], 'no timings recorded for the base commit')
        api.list.return_value = [{'status': 'in_progress'}]
        result = report.baseline_reports(api, 'sha', 'tree', dict.fromkeys(report.ARCHES, pr), 42)
        self.assertEqual(result['arm'], 'baseline run in progress')
        api.timings.return_value = [partial, other_cpu], []
        self.assertEqual(report.missing(api, 'tree'), [])

    def test_profile_warning_keeps_times_and_alerts(self):
        base = timing(proof('a', 300), cpu='Intel(R) Xeon(R) Platinum 8124M CPU @ 3.00GHz')
        pr = timing(proof('a', 120), cpu='Intel(R) Xeon(R) Platinum 8223CL CPU @ 3.00GHz')
        table, alerts, eligible = report.section('arm', pr, base)
        self.assertEqual(table.title, 'Full results · ARM · 1 proof · ⚠️ CPU differs '
                                      '(Xeon Platinum 8124M vs Xeon Platinum 8223CL)')
        self.assertIn('300 s | 120 s | −180 s (−60.0%)', table.rows[0])
        self.assertIn('300 s | 120 s | −180 s (−60.0%)', table.rows[1])
        self.assertEqual([row.split(' | ')[1] for _, row in alerts], ['Improvement', 'Improvement'])
        self.assertTrue(eligible)
        major = report.build_report({'arm': pr, 'x86': pr}, {'arm': base, 'x86': pr})[0]
        self.assertEqual(major.intro, '⚠️ ARM: CPU differs (Xeon Platinum 8124M vs Xeon Platinum 8223CL)')
        self.assertIn('### Major changes\n\n⚠️ ARM: CPU differs', major.render())
        self.assertEqual(len(major.rows), 2)
        same = report.build_report({'arm': base, 'x86': pr}, {'arm': base, 'x86': pr})[0]
        self.assertEqual((same.intro, same.note), ('', 'No major changes for ARM and x86.'))
        del pr['profile']['os']
        self.assertIn('os not recorded', report.section('arm', pr, base)[0].title)
        pr['profile']['cpu'] = '<model>'
        table, _, _ = report.section('arm', pr, base)
        self.assertIn('&lt;model&gt;', table.render())
        self.assertEqual(report.cpu_models('Xeon CPU @ 2.00GHz', 'Xeon CPU @ 3.00GHz'),
                         'Xeon CPU @ 2.00GHz vs Xeon CPU @ 3.00GHz')

    def test_reciprocal_thresholds(self):
        # Exercise each limit exactly and immediately below it in both directions.
        for total, cases in [
            (False, [(10, 20, True), (9, 19.9, False), (10.1, 20, False),
                     (20, 30, True), (20.1, 30, False), (0, 20, True)]),
            (True, [(240, 300, True), (241, 301, False), (200, 259, False), (0, 100, False)]),
        ]:
            for low, high, qualifies in cases:
                for before, after, direction in [(low, high, 'Regression'), (high, low, 'Improvement')]:
                    with self.subTest(before=before, after=after, total=total):
                        alerts = []
                        report.add_major_change(alerts, 'ARM', 'proof', before, after, total=total)
                        self.assertEqual(bool(alerts), qualifies)
                        if qualifies:
                            self.assertIn(direction, alerts[0][1])
        self.assertEqual(report.change(0, 20), '+20 s')
        self.assertEqual(report.change(300, 240), '−60 s (−20.0%)')

    def test_total_only_and_stable_order(self):
        base = timing(*(proof(str(n), 24) for n in range(10)))
        pr = timing(*(proof(str(n), 30) for n in range(10)))
        tables = report.build_report({'arm': pr, 'x86': base}, {'arm': base, 'x86': pr})
        self.assertEqual(len(tables[0].rows), 2)
        self.assertIn('ARM **Total** (10 matched routines) | Regression', tables[0].rows[0])
        self.assertIn('x86 **Total** (10 matched routines) | Improvement', tables[0].rows[1])
        pr['targets'].extend([proof('only-pr', 1000), proof('spec', 1000, 'spec check')])
        base['targets'].extend([proof('only-base', 800), proof('spec', 1, 'spec check')])
        tables = report.build_report({'arm': pr, 'x86': pr}, {'arm': base, 'x86': base})
        self.assertEqual(len(tables[0].rows), 4)
        self.assertIn('x86 **Total**', tables[0].rows[1])
        self.assertIn('ARM `spec.correct` (spec check)', tables[0].rows[2])
        self.assertIn('240 s | 300 s | +60 s (+25.0%)', tables[1].rows[0])
        self.assertFalse(any('only-base' in row for row in tables[1].rows))
        self.assertTrue(any('only-pr.correct` | Added | — | 1,000 s | —' in row for row in tables[1].rows))

    def test_partial_and_missing_measurements(self):
        base = timing(proof('a', 20), proof('b', 50))
        partial = timing(proof('a', 40), proof('b', 'unconfirmed'), success=False)
        table, alerts, eligible = report.section('arm', partial, base)
        self.assertTrue(eligible)
        self.assertEqual(len(alerts), 1)
        self.assertIn('Incomplete | 50 s | unconfirmed | —', table.rows[1])
        self.assertIn('Incomplete | 70 s | — | —', table.rows[0])
        table, alerts, eligible = report.section('arm', base, partial)
        self.assertTrue(eligible)
        self.assertEqual(len(alerts), 1)
        self.assertIn('Base incomplete', table.title)
        self.assertIn('40 s | 20 s | −20 s (−50.0%)', table.rows[2])
        table, alerts, _ = report.section('arm', base, 'missing')
        self.assertIn('Base unavailable | — | 70 s', table.rows[0])
        self.assertFalse(alerts)
        self.assertFalse(any('Added' in row for row in table.rows))
        self.assertEqual(report.section('arm', 'missing', base)[0].rows, [])
        empty = dict.fromkeys(report.ARCHES, 'missing')
        tables = report.build_report(empty, empty)
        self.assertEqual(tables[0].note, 'No architecture has comparable timings.')
        for table in tables[1:]:
            self.assertIn('No proof timings available.', table.render())
        table, alerts, _ = report.section('arm', base, timing(proof('c', 20)))
        self.assertIn('No matched routines | — | — | —', table.rows[0])
        self.assertFalse(alerts)

    def test_select_by_slower_side(self):
        # Slower sides: a 40, b 700, c 900, d 650 (base only), f 1500 (base).
        # `e` is only in the base and never selected.
        pr = timing(proof('a', 40), proof('b', 700), proof('c', 900), proof('d', 'not run'),
                    proof('f', 500), success=False)
        base = timing(proof('a', 5), proof('b', 30), proof('c', 100), proof('d', 650),
                      proof('e', 2000), proof('f', 1500))
        for count, min_seconds, kept in [(None, None, 'abcdf'), (2, None, 'cf'), (None, 600, 'bcdf'),
                                         (1, 600, 'f'), (3, 50, 'bcf')]:
            with self.subTest(count=count, min_seconds=min_seconds):
                current, old = report.select_proofs(pr, base, count, min_seconds)
                self.assertEqual(''.join(row['target'][0] for row in current['targets']), kept)
                self.assertEqual(''.join(row['target'][0] for row in old['targets']), kept)
        # `f` improved below the threshold and is still reported; `a` is not.
        current, old = report.select_proofs(pr, base, None, 600)
        tables = report.build_report({'arm': current, 'x86': 'missing'}, {'arm': old, 'x86': base})
        self.assertEqual([row.split('`')[1] for row in tables[0].rows],
                         ['f.correct', 'c.correct', 'b.correct'])
        self.assertIn('Improvement', tables[0].rows[0])
        self.assertIn('Incomplete | 650 s | not run', tables[1].rows[1])
        self.assertFalse(any('a.correct' in row for table in tables for row in table.rows))
        self.assertEqual(report.select_proofs('missing', base, None, 600), ('missing', dict(base, targets=[])))
        self.assertEqual(report.select_proofs('missing', base, None, None)[1]['targets'], [])
        self.assertEqual(report.scope_note(150, 600), 'Showing, per architecture, the 150 slowest proofs '
                         'that took at least 600 s, by the slower of their base and PR times.')
        self.assertEqual(report.scope_note(None, None), '')
