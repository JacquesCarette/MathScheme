#!/usr/local/bin/perl
#
# File: MS-xtr.pl
#  Extracts contents of LaTeX environments from a LaTeX file.
#  By default, extracting MathScheme library program code in <theory> 
#  environment with a marker pattern %%@ of different target files.
#
# Options:
#  -a - extract all code into different target files, do not use it
#       together with <codefile>
#  -e<environment> - extract content of <environment>; default is
#                    <theory> environment
#  -p<pattern> - marker pattern for environments to extract (see below)
#                a null pattern is possible
#  -h - usage and synopsis of standard options
#
# NOTE: This program requires Perl 5. You may need modify the first line
# according to the location of Perl 5 on your system.
#
$|=1;
$all=0;
$ncode=0;
unless (defined @ARGV) { &usage; }
foreach (@ARGV) {
  OPTION: {
  	  # extract all
      ($_ eq "-a") && do { $all=1; last OPTION; };
      # choose non-default environment type
      ($_ =~ /^-e/) && do {
	$envtype=substr($_,2);
	last OPTION;
      };
      # choose non-default marker pattern
      ($_ =~ /^-p/) && do {
	$mpatt=substr($_,2);
	$mpatt =~ s/\@/\\\@/g;
	$mpatt =~ s/\+/\\\+/g;
	last OPTION;
      };
      ($_ eq "-h") && do { &usage; }; # show help
      if (defined $texfile) {
      	  # target code file if specified
          if ($all == 1) { print "<codefile> $_ ignored.\n"; last OPTION; }
          $codefile=$_;
      } else {
      	  # latex source file
          $texfile=$_;
      };
  };
}

# check arguments, set defaults if necessary
unless (defined $texfile) { die "Error: No <texfile> specified.\n"; }
unless (defined $envtype) { $envtype="theory"; }
unless (defined $mpatt) { $mpatt="%%\@"; }

# process latex source file
open(TEX,"$texfile");
if ($all == 0) {
# search with specific codefile or extract all into one file
# if no codefile name is given, the default name is "xtr-out.msl"
    if (defined $codefile) {
      $fpatt="$mpatt $codefile";
    } else {
      $codefile="lib.msl";
      $fpatt=$mpatt;
    }
    open(CODE,">$codefile");
    while ($line = <TEX>) {
        if ($line =~ /^$fpatt/) {
            unless ($fpatt eq "") { $line = <TEX>; } # null pattern is special
            if ($line =~ /\\begin\{$envtype\}/gi) {
		$nested=1;
                while ($line = <TEX>) {
                    if ($line =~ /\\end\{$envtype\}/gi) {
			--$nested;
			if ($nested == 0) { last; }
		    } elsif ($line =~ /\\begin\{$envtype\}/gi) { ++$nested; }
                    ++$ncode;
                    print CODE $line;
                }
            }
        }
    }
    close(CODE);
    print "$ncode lines of extracted code written to $codefile.\n";
} else {
# extract and distribute into individual codefiles
  while ($line = <TEX>) {
    if ($line =~ /^$mpatt/) {
      $codefile=substr($line,(length $mpatt));
      chomp $codefile;
      # count number of output files
      unless (defined $ncode{$codefile}) { ++$nfiles; }
      open(CODE,"+>>$codefile");
      $line = <TEX>;
      if ($line =~ /\\begin\{$envtype\}/gi) {
	  $nested{$codefile}=1;
	  while ($line = <TEX>) {
	      if ($line =~ /\\end\{$envtype\}/gi) {
		  --$nested{$codefile};
		  if ($nested{$codefile} == 0) { last; }
	      } elsif ($line =~ /\\begin\{$envtype\}/gi) {
		  ++$nested{$codefile};
	      }
	      ++$ncode{$codefile};
	      print CODE $line;
	  }
      }
      close(CODE);
    }
  }
  print "$ncode lines of extracted code written to $codefile.\n";
  format STDOUT_TOP=
@<<<file@>>>>>>>>>>>>>>>>>>>>>>>>>>>> no. of lines

--------------------------------------------------
.
  write;
  format STDOUT=
   @<<<<<<<<<<<<<<<<<<<<<<<<<<@>>>>>>>>>>>>>>>>>>>
$outfile,$nlines
.
  foreach (keys %ncode) {
    $outfile=$_;
    $nlines=$ncode{$_};
    write;
  }
}
close(TEX);
exit;

# specify usage and options
sub usage {
    print "Usage: MS-xtr.pl <options> texfile <codefile>
Options:
  -a - extract all code into different target files, do not use it
       together with <codefile>
  -e<environment> - extract content of <environment>; default is
                    <theory> environment
  -p<pattern> - marker pattern for environments to extract (see below)
                a null pattern is possible
  -h - usage and synopsis of standard options

texfile is a LaTeX source file containing code of LaTeX environment. The 
environment containing the code must be preceded by a line beginning with
a marker pattern (%%\@ by default), optionally followed by a program source
name <codefile>.\n";
    exit;
}

