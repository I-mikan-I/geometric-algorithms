#!/bin/sh

find . -name '*.rkt' -exec raco fmt -i {} \;