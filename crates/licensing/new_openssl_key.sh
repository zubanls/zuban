openssl genpkey -algorithm Ed25519 -text \
    | sed 's/ //g' \
    | rg priv: -A 7 \
    | sed ':a;N;$!ba;s/:\n/:/g' \
    | sed 's/pub:/pub:  /' \
    | sed 's/priv:/priv: /'
