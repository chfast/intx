#!/usr/bin/env sh

processes_to_stop='firefox clion.sh goland.sh smartgit.sh'

cpulist='0,4'

get_pids_with_children() {
  local pids=''
  local new_pids
  local children_pids

  new_pids=$(pgrep --exact --oldest "$1")

  while [ "$new_pids" ]; do
    pids="$pids $new_pids"

    children_pids=''
    for pid in $new_pids; do
      children_pids="$children_pids $(pgrep --parent "$pid" --delimiter ' ')"
      children_pids=${children_pids## } # Strip leading space if any.
    done

    new_pids="$children_pids"
  done

  echo ${pids## }
}

pids=''
for name in $processes_to_stop; do
  new_pids=$(get_pids_with_children $name)
  if [ "$new_pids" ]; then
    pids="$pids $new_pids"
  fi
done

if [ "$pids" ]; then
  echo "Stopping: $processes_to_stop\n   (pids:$pids)"
  kill -STOP $pids
fi

# Continue script in case of SIGINT to cleanup and resume stopped processes.
trap 'echo Interrupted...' 2

echo 1 | sudo tee /sys/devices/system/cpu/intel_pstate/no_turbo >/dev/null
sudo cpupower frequency-set -g performance >/dev/null
sudo cset shield --cpu=$cpulist -k on

sleep 3

echo "\nExecuting '$@'"
cset shield -- sudo cpupower --cpu $cpulist monitor "$@"

sudo cset shield --reset
sudo cpupower frequency-set -g powersave >/dev/null
echo 0 | sudo tee /sys/devices/system/cpu/intel_pstate/no_turbo >/dev/null

if [ "$pids" ]; then
  echo "Resuming stopped processes..."
  kill -CONT $pids
fi
