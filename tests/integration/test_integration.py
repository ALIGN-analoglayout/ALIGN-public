import pytest
import align
import os
import pathlib

run_flat = {'linear_equalizer',
            'variable_gain_amplifier',
            'single_to_differential_converter'}

skip_pdks = {'Bulk65nm_Mock_PDK',
             'Nonuniform_mock_pdk'}

skip_dirs = {'Sanitized_model3x_MDLL_TOP',
             'OTA_FF_2s_v3e',
             'Sanitized_Coarse_SAR_Logic',
             'ADC_CORE',
             'GF65_DLL_sanitized',
             'Sanitized_5b_ADC',
             'Sanitized_CDAC_SW_Coarse',
             'Sanitized_DLPF_RCFilter',
             'Sanitized_TempSensor',
             'CTDTDSM_V3',
             'single_SAR',
             'Sanitized_civiR_DLDO_TOP',
             'Sanitized_TX_8l12b',
             'Santized_12b_ADC_TOP',
             'Sanitized_LevelCrossingDetector',
             'Sanitized_CK_Divider8',
             'mimo_bulk'}


ALIGN_HOME = pathlib.Path(__file__).parent.parent.parent

pdks = [pdk for pdk in (ALIGN_HOME / 'pdks').iterdir() if pdk.is_dir() and pdk.name not in skip_pdks]


def gen_examples():
    ci_level = os.environ.get('CI_LEVEL', 'all')

    examples_dir = ALIGN_HOME / 'examples'
    examples = [p.parents[0] for p in examples_dir.rglob('*.sp') if all(x not in skip_dirs for x in p.relative_to(examples_dir).parts)]

    if ci_level == 'merge':
        circle_ci_skip = "not SAR and not Sanitized_EdgeComparator and not DLL and not single_to_differential_converter and not COMPARATOR_2LEVEL_BIDIRECTIONAL_MAC_SKEW and not CTD and not BUFFER_VREFP and not BUFFER_VREFP2 and not CTDSM_CORE_NEW and not BUFFER_VCM and not vco_dtype_12_hierarchical and not Sanitized_Coarse_Comp_CK and not COMP_GM_STAGE_0415 and not linear_equalizer and not test_vga and not Gm1_v5_Practice and not powertrain_binary and not SW_Cres_v3_5 and not ldo_error_amp and not telescopic_ota_guard_ring"
        exclude_strings = [nm for nm in circle_ci_skip.split(' ') if nm not in ["and", "or", "not"]]

        additional_skip_dirs = set()
        for p in examples:
            s = str(p)
            if any(x in s for x in exclude_strings):
                additional_skip_dirs.add(p.stem)
        print(additional_skip_dirs)

        examples = [p.parents[0]
                    for p in examples_dir.rglob('*.sp')
                    if all(x not in skip_dirs and x not in additional_skip_dirs
                    for x in p.relative_to(examples_dir).parts)]
    elif ci_level == 'checkin':
        circle_ci_dont_skip = "adder or switched_capacitor_filter or high_speed_comparator"
        include_strings = [nm for nm in circle_ci_dont_skip.split(' ') if nm not in ["or"]]
        restricted_directories = set()
        for p in examples:
            s = str(p)
            if any(x in s for x in include_strings):
                restricted_directories.add(p.stem)

        print(restricted_directories)
        examples = [p.parents[0]
                    for p in examples_dir.rglob('*.sp')
                    if all(x not in skip_dirs for x in p.relative_to(examples_dir).parts)
                    and any(x in restricted_directories for x in p.relative_to(examples_dir).parts)]
    elif ci_level == 'all':
        pass
    else:
        assert False, ci_level

    print(examples)
    return examples


@pytest.mark.nightly
@pytest.mark.parametrize("design_dir", gen_examples(), ids=lambda x: x.name)
@pytest.mark.parametrize("pdk_dir", pdks, ids=lambda x: x.name)
def test_integration(pdk_dir, design_dir, maxerrors, router_mode, skipGDS):
    uid = os.environ.get('PYTEST_CURRENT_TEST')
    uid = uid.split(' ')[0].split(':')[-1].replace('[', '_').replace(']', '').replace('-', '_')
    run_dir = pathlib.Path(os.environ['ALIGN_WORK_DIR']).resolve() / uid
    run_dir.mkdir(parents=True, exist_ok=True)
    os.chdir(run_dir)

    nm = design_dir.name

    args = [str(design_dir), '-f', str(design_dir / f"{nm}.sp"), '-s', nm, '-p', str(pdk_dir),
            '-flat',  str(1 if nm in run_flat else 0), '-l', 'WARNING', '-v', 'INFO']
    args.extend(['--router_mode', router_mode])

    if skipGDS:
        args.extend(['--skipGDS'])
    else:
        args.extend(['--regression'])

    results = align.CmdlineParser().parse_args(args)

    assert results is not None, f"{nm} :No results generated"
    for result in results:
        _, variants = result
        for (k, v) in variants.items():
            assert 'errors' in v, f"No Layouts were generated for {nm} ({k})"
            assert v['errors'] <= maxerrors, f"{nm} ({k}):Number of DRC errorrs: {str(v['errors'])}"
