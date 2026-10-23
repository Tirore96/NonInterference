# Regenerate the name -> file:line table for \m{...} links before every build.
system("python3", "mechlinks.py") == 0 or die "mechlinks.py failed\n";
