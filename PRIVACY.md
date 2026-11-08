# Privacy Policy

_Last updated: 8 November 2026_

NXDomain'd is a free, open-source browser extension that finds requests your browser makes to unregistered domains.

## Summary

NXDomain'd has no accounts, analytics, advertising or tracking, and the developer receives no data from it. To check whether a domain is registered, it sends that domain name to public lookup services.

## Data sent to lookup services

For each new domain your browser loads something from, NXDomain'd sends the domain name, and nothing else, to:

- [rdap.org](https://rdap.org/), and the registry's RDAP server it redirects to, to look up the registration.
- [Google Public DNS](https://dns.google/) and [Cloudflare DNS](https://cloudflare-dns.com/), as a fallback when RDAP gives no answer.

These services see your IP address, as with any web request. Their own privacy policies apply.

## Data stored in your browser

The domains it has checked, their results, and the pages and request URLs it saw them on stay in your browser's extension storage. **Clear list** in the popup deletes them, and so does removing the extension.

## Permissions

- **Access to all websites, webRequest, webNavigation and tabs:** to see which domains pages load from.
- **Storage:** to keep the list of domains between browser restarts.

## Changes

Any changes to this policy will be made in this file. Its full history is in this repository's commit log.

## Contact

For questions about this policy, open an issue at <https://github.com/MegaManSec/NXDOMAIND/issues>.
