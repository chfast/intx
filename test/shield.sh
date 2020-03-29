#!/usr/bin/env sh

killall -STOP 'firefox'
killall -STOP 'Web Content'
killall -STOP 'GPU Process'
killall -STOP 'RDD Process'
killall -STOP 'WebExtensions'
killall -STOP 'java'
#killall -STOP 'gnome-shell'

sudo cset shield --cpu=0,4 -k on
sudo cpupower frequency-set -g performance
echo 1 | sudo tee /sys/devices/system/cpu/intel_pstate/no_turbo > /dev/null

sleep 1

cset shield -- "$@"

echo 0 | sudo tee /sys/devices/system/cpu/intel_pstate/no_turbo > /dev/null
sudo cpupower frequency-set -g powersave
sudo cset shield --reset

#killall -CONT 'gnome-shell'
killall -CONT 'java'
killall -CONT 'WebExtensions'
killall -CONT 'RDD Process'
killall -CONT 'GPU Process'
killall -CONT 'Web Content'
killall -CONT 'firefox'
