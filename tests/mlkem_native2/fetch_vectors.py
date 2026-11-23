# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

# Download the ACVP and Wycheproof ML-KEM vectors that mlkem-native's
# clients use, with the clients' own download functions and pinned
# versions, into test/acvp/.acvp-data and test/wycheproof/.wycheproof-data
# under the current directory.
#
# usage: python3 fetch_vectors.py MLKEM_NATIVE_CHECKOUT

import sys


def load(name, path):
    src = open(path).read()
    # Keep the definitions only: drop the argument parsing and main code
    cut = src.index('parser = argparse.ArgumentParser')
    mod = type(sys)(name)
    exec(compile(src[:cut], path, 'exec'), mod.__dict__)
    return mod


m = sys.argv[1]
a = load('acvp', m + '/test/acvp/acvp_client.py')
print('acvp', a.download_acvp_files('v1.1.0.43'))
w = load('wyche', m + '/test/wycheproof/wycheproof_client.py')
print('wycheproof', w.download_wycheproof_files(
    w.get_wycheproof_data_dir('test/wycheproof/.wycheproof-data')))
