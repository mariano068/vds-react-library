import { storiesOf } from '@storybook/react';
import React from 'react';
import { muiTheme } from 'storybook-addon-material-ui5';
import VdsBreadcrumbDefaultStory from '../snippets/VdsBreadcrumb.snippets';

import { version } from '../../../package.json';

storiesOf(`vds@${version}`, module)
  .addDecorator(muiTheme())
  .add('Breadcrumb', () => (
    <VdsBreadcrumbDefaultStory />
  ));
