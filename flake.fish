set common \
  '--no-libraries' \
  "--include-path=$NIX_ROOT/src" \

set --export AGDA_ARGS $common \
  '--local-interfaces'
set --export AGDA_UNUSED_ARGS $common

function check-unused
  agda-unused --global $AGDA_UNUSED_ARGS "$NIX_ROOT/src/All.agda"
end

function check-agda
  echo; echo 'Checking Agda code:'; echo
  agda $AGDA_ARGS "$NIX_ROOT/src/All.agda"; or return $status
  echo 'All done.'

  echo; echo 'Checking for unused code:'; echo
  check-unused
end

