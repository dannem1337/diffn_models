if [[ "${BASH_SOURCE[0]}" = "${0}" ]]; then
    >&2 echo "Remember: you need to run me as 'source ${0}', not execute it!"
    exit
fi

# Create or activate Python virtual environment
source ~/.venvs/mzn/bin/activate

# Set other environment variables and load cluster modules
module load MiniZinc/2.8.7 Gecode/e86200e4f12489c8b6078df3bac7638745c03010-GCCcore-9.3.0 Chuffed/e04bedd06c3eee88f318372a8a1ed35c954ba9d4-GCCcore-9.3.0
