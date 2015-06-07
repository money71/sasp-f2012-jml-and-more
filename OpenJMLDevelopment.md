Based upon this wiki - this works (TM) for us:


## Setup trunk / branches etc ##

Create a standalone folder/workspace for the code:

```

    $ cat open_jml_trunk_sourcecode/svn_update.sh 
    #!/bin/sh

    svn co https://jmlspecs.svn.sourceforge.net/svnroot/jmlspecs/JMLAnnotations/trunk JMLAnnotations
    svn co https://jmlspecs.svn.sourceforge.net/svnroot/jmlspecs/OpenJML/trunk/OpenJDK OpenJDK
    svn co https://jmlspecs.svn.sourceforge.net/svnroot/jmlspecs/OpenJML/trunk/OpenJML OpenJML
    svn co https://jmlspecs.svn.sourceforge.net/svnroot/jmlspecs/OpenJML/trunk/OpenJML-UpdateSite OpenJML-UpdateSite
    svn co https://jmlspecs.svn.sourceforge.net/svnroot/jmlspecs/OpenJML/trunk/OpenJMLFeature OpenJMLFeature
    svn co https://jmlspecs.svn.sourceforge.net/svnroot/jmlspecs/OpenJML/trunk/OpenJMLUI OpenJMLUI
    svn co https://jmlspecs.svn.sourceforge.net/svnroot/jmlspecs/Specs/trunk Specs
    svn co https://jmlspecs.svn.sourceforge.net/svnroot/jmlspecs/OpenJML/vendor vendor

```

Create a separate Eclipse workspace which contains no code:

```

    $ ls -a open_jml_trunk_workspace
    .  ..  .metadata

```

Get a **fresh** Eclipse sdk (both 32/64 bit 3.7.2 worked for us).

Start that eclipse using the **empty** workspace.

Then import as Eclipse existing projects (without copying):
- JMLAnnotations
- OpenJDK
- OpenJML
- OpenJML-UpdateSite
- OpenJMLFeature
- OpenJMLUI
- Specs

Then at least clean projects and build.

Turn off auto build since it otherwise will build projects each time we save.

## Trouble shooting on import ##

Turn on show all **.** resources under the **filters** e.g. add exception
for **.svn which we dont wanna see.**

We experienced an import error on a non existing src folder:
http://screencast.com/t/n0eiUUzQV

Clean and build project again then it rasises error:

> Project 'OpenJML' is missing required Java project: 'Specs'

Simply import Specs again and clean rebuild all projects at the same
time again.

And now no errors in the log **only** a bunch of warnings.

