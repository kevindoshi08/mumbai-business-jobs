# Mumbai & remote business jobs

A public job board for HR, administration, executive assistant, operations, management, and sales and marketing roles. It lists roles in the Mumbai region and remote roles that explicitly accept candidates in India or Asia-Pacific.

Live dashboard: https://kevindoshi08.github.io/mumbai-business-jobs/

## How it works

GitHub Actions runs `tracker.py` around 9 am and 6 pm IST. Each run:

1. Reads public job feeds and official employer job boards listed in `config.json`: Workable job search, Amazon Jobs, JPMorganChase, 37 Workday career sites, 15 Greenhouse, Lever, Ashby, and SmartRecruiters boards, Himalayas, Remotive, Jobicy, Working Nomads, and We Work Remotely.
2. Keeps roles whose titles match the six role families, and drops engineering, finance, legal, clinical, director-level, internship, and similar roles.
3. Keeps Mumbai-region roles and remote roles open to India. Roles that clearly ask for more than five years of experience are dropped; manager and lead titles are marked as stretch roles.
4. Updates `data/jobs.json`, which records when each role was first and last seen.
5. Publishes the dashboard to GitHub Pages.

The tracker never applies to jobs, contacts anyone, or copies LinkedIn, Naukri, or Indeed listings. The dashboard links to live searches on those sites instead.

## Run it locally

Python 3.10 or newer is enough; there are no packages to install.

```sh
python3 tracker.py run -v      # fetch roles, update data/jobs.json, build site/index.html
python3 tracker.py build       # rebuild site/index.html from data/jobs.json
```

To refresh the public dashboard immediately, open the repository's Actions tab, choose **Refresh job board**, and select **Run workflow**.

## Change what it tracks

Edit `config.json`:

- `workday`, `oracle`, and `boards` list employer career sites.
- `sources.workable.mumbai_queries` and `remote_queries` control Workable searches.
- `filters.max_years_required` sets the experience cutoff, and `max_age_days` drops old postings.
- `search_links` controls the LinkedIn, Naukri, and Indeed shortcuts.

Role and location rules live near the top of `tracker.py`.

Applied and hidden marks on the dashboard are stored in each visitor's browser, so they are private to that browser.
