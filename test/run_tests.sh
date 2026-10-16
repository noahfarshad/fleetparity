#!/bin/bash
# Self-contained: certificate, eight mock managers and vCenters, the flows, cleanup.   bash test/run_tests.sh
#   9443 Green GM   9444 Blue GM   9445 Green site-a LM   9446 Blue site-a LM   9447 Green site-b LM
#   9448 Blue site-a vCenter   9449 Blue site-b vCenter   9450 Green vCenter
# ssh and ping are the fakes in test/bin, driven by test/world.json and the mocks' state.
# Each flow resets the mocks first and prints what each run did:
#   undo_flow2.py      (runs undo_flow.py first) every step forward and its way back
#   wave_flow.py       the three steps by a wave .csv in the config, and back
#   wave_test_flow.py  the same with --test while the scope is wider: only the test segment is written
#   signin_flow.py     fp --by-site puts every sign-in in its site; a refused edge password is named
#   simple_flow.py     1.23.0 and 1.24.0, asserted: builds need --expect outside --test, --return --vm, NEXT, held changes, folders
set -e
cd "$(dirname "$0")"
PORTS="9443 9444 9445 9446 9447 9448 9449 9450"
for port in $PORTS; do
  if python3 -c "import socket; socket.create_connection(('127.0.0.1', $port), timeout=0.5)" 2>/dev/null; then
    echo "port $port is in use - stop the old mock and re-run"; exit 2; fi
done
openssl req -x509 -newkey rsa:2048 -nodes -keyout k.pem -out c.pem -days 1 -subj "/CN=127.0.0.1" 2>/dev/null
PIDS=""
for spec in green-gm:9443 blue-gm:9444 green-lm:9445 lm:9446 lm:9447 vc:9448 vc:9449 vc:9450; do
  python3 mock_nsx.py "${spec%%:*}" "${spec##*:}" c.pem k.pem >> mock.log 2>&1 &
  PIDS="$PIDS $!"
done
trap 'kill $PIDS 2>/dev/null; rm -f k.pem c.pem mock.log world.json migpath_state_* migpath_*_site-a.csv switch_requirements.txt env.*.yaml.* wave1.csv; rm -rf out' EXIT
export PATH="$PWD/bin:$PATH" FP_TEST_WORLD="$PWD/world.json"
sleep 1.5
for m in $PIDS; do kill -0 $m 2>/dev/null || { echo "a mock failed to start:"; cat mock.log; exit 2; }; done
for flow in ${@:-undo_flow2.py wave_flow.py wave_test_flow.py signin_flow.py simple_flow.py}; do
  echo "################################ $flow"
  python3 "$flow"
done
